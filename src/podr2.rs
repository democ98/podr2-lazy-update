use std::{
    collections::HashSet,
    convert::From,
    fs,
    io::{Read, Seek, SeekFrom},
    str::FromStr,
    sync::{Arc, mpsc::channel},
};
use crypto::{digest::Digest, sha2::Sha256};
use hex;
use num_bigint::{BigUint, ToBigUint};
use num_bigint_dig::RandBigInt;
use num_integer::Integer;
use num_traits::Zero;
use rand::{Rng, RngCore};
use rsa::{Pkcs1v15Sign, PublicKey, PublicKeyParts, rand_core::OsRng, RsaPrivateKey, RsaPublicKey};
use rsa::pkcs1::{EncodeRsaPublicKey};
// use rsa::pkcs8::{DecodePrivateKey};
use serde::{Deserialize, Serialize};
use threadpool::ThreadPool;

#[derive(Debug)]
pub enum FailCode {
    InternalError(String),
    ParameterError(String),
}

#[derive(Debug)]
pub struct PDPError {
    pub error_code: FailCode,
}

impl std::fmt::Display for FailCode {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            FailCode::InternalError(s) => write!(f, "{}", s),
            FailCode::ParameterError(s) => write!(f, "{}", s),
        }
    }
}

#[derive(Clone)]
pub struct Keys {
    pub skey: RsaPrivateKey,
    pub pkey: RsaPublicKey,
}

// The struct of the calculation result of the sig_gen() function
#[derive(Serialize, Deserialize, Clone, Debug)]
#[serde(rename_all = "snake_case")]
pub struct Tag {
    pub t: T,
    pub phi_hash: String,
    pub attest: String,
}

impl Default for Tag {
    fn default() -> Self {
        Tag {
            t: T { name: "".to_string(), u: "".to_string(), phi: vec![] },
            phi_hash: "".to_string(),
            attest: "".to_string(),
        }
    }
}

//Information about the file
#[derive(Serialize, Deserialize, Clone, Debug)]
#[serde(rename_all = "snake_case")]
pub struct T {
    pub name: String,
    pub u: String,
    pub phi: Vec<String>,
}

//The W structure that needs to be used when calculating sigma
#[derive(Serialize, Clone, Debug)]
pub struct W {
    name: String,
    i: u64,
}

impl W {
    fn new() -> W {
        W { name: "".to_string(), i: 0 }
    }

    fn hash(&mut self) -> Vec<u8> {
        let mut hasher = Sha256::new();
        hasher.input(self.name.as_bytes());
        hasher.input(format!("{}", self.i).as_bytes());
        let mut hash_result = vec![0u8; hasher.output_bytes()];
        hasher.result(&mut hash_result);
        hash_result
    }
}

/*
	Challenge Part
*/

#[derive(Serialize, Clone, Deserialize, Debug)]
#[serde(rename_all = "snake_case")]
pub struct QElement {
    pub i: u64,
    pub v: Vec<u8>,
}

impl QElement {
    fn new() -> Self {
        QElement { i: 0, v: Vec::new() }
    }
}

pub trait HashSelf {
    fn new() -> Self;
    fn load_field(&mut self, d: &[u8]);
    fn c_hash(&mut self) -> Vec<u8>;
}

impl Keys {
    pub fn sig_gen<H: HashSelf>(
        &self,
        file_path: &String,
        n_blocks: u64,
        name: &String,
        mut h: H,
        pool: ThreadPool,
    ) -> Result<Tag, PDPError> {
        let mut result = Tag {
            t: T { name: "".to_string(), u: "".to_string(), phi: vec![] },
            phi_hash: "".to_string(),
            attest: "".to_string(),
        };
        //generate u
        let mut rng = rand::thread_rng();
        let u_tmp = rng.gen_biguint_range(&Zero::zero(), self.pkey.n());
        let u = Arc::new(
            num_bigint::BigUint::from_str(&u_tmp.to_string())
                .map_err(|e| PDPError { error_code: FailCode::InternalError(e.to_string()) })?,
        );
        //open a file
        let mut f = fs::File::open(file_path)
            .map_err(|e| PDPError { error_code: FailCode::ParameterError(e.to_string()) })?;

        //detect file size
        let file_size = match f.seek(SeekFrom::End(0)) {
            Ok(s) => s,
            Err(e) => {
                return Err(PDPError { error_code: FailCode::InternalError(e.to_string()) });
            }
        };
        if file_size % n_blocks != 0 {
            return Err(PDPError {
                error_code: FailCode::InternalError(format!(
                    "The size of file {:?} is {}, which cannot be divisible by {} blocks",
                    name, file_size, n_blocks
                )),
            });
        };

        let each_chunks_size = file_size / n_blocks;
        let mut offset = 0_u64;

        let (tx, rx) = channel();
        result.t.phi = vec!["".to_string(); n_blocks as usize];
        for i in 0..n_blocks {
            let mut chunks = vec![0u8; each_chunks_size as usize];

            let _ = f.seek(SeekFrom::Start(offset));
            match f.read_exact(&mut chunks) {
                Ok(_) => {}
                Err(e) => {
                    return Err(PDPError {
                        error_code: FailCode::InternalError(format!(
                            "Fail in read file :{:?}",
                            e.to_string()
                        )),
                    });
                }
            };

            let tx = tx.clone();
            let u = u.clone();
            let ssk = self.skey.clone();
            let name = name.clone();
            pool.execute(move || {
                tx.send((generate_sigma(ssk, chunks, name, i, u), i)).unwrap();
            });
            offset += each_chunks_size;
        }
        let iter = rx.iter().take(n_blocks as usize);
        let mut phi_hasher = Sha256::new();
        for k in iter {
            result.t.phi[k.1 as usize] = k.0.clone();
            phi_hasher.input(k.0.as_bytes());
        }
        let mut phi_hash = vec![0u8; phi_hasher.output_bytes()];
        phi_hasher.result(&mut phi_hash);

        result.t.name = name.clone();
        result.t.u = u.clone().to_string();
        result.phi_hash = hex::encode(phi_hash.clone());

        h.load_field(&name.as_bytes());
        h.load_field(&u.clone().to_string().as_bytes());
        h.load_field(&phi_hash);
        let attest = self.sign_data(&h.c_hash())?;
        result.attest = hex::encode(attest);

        Ok(result)
    }

    pub fn proof_gen(
        &self,
        file_path: String,
        q_slice: Vec<QElement>,
        t: Tag,
    ) -> Result<Proof, PDPError> {
        let n = num_bigint::BigUint::from_bytes_be(&self.pkey.n().to_bytes_be());
        let mut mu = 0.to_biguint().unwrap();
        let mut sigma = 1.to_biguint().unwrap();
        let block_num = t.t.phi.len();
        //open a file
        let mut f = fs::File::open(file_path)
            .map_err(|e| PDPError { error_code: FailCode::ParameterError(e.to_string()) })?;

        let file_size = match f.seek(SeekFrom::End(0)) {
            Ok(s) => s,
            Err(e) => {
                return Err(PDPError { error_code: FailCode::ParameterError(e.to_string()) });
            }
        };

        let each_size = file_size / block_num as u64;
        for q in q_slice {
            let _ = f.seek(SeekFrom::Start(each_size * q.i));
            let mut data = vec![0u8; each_size as usize];
            let _ = f.read(&mut data);

            //µ =Σ νi*mi ∈ Zp (i ∈ [1, n])
            let vi = num_bigint::BigUint::from_bytes_be(&q.v);
            let mi = num_bigint::BigUint::from_bytes_be(&data);
            mu = vi.clone() * mi + mu;

            //σ =∏ σi^vi ∈ G (i ∈ [1, n])
            let mut sigma_i = num_bigint::BigUint::from_str(&t.t.phi[q.i as usize])
                .map_err(|e| PDPError { error_code: FailCode::InternalError(e.to_string()) })?;
            sigma_i = sigma_i.modpow(&vi, &n);
            sigma = sigma * sigma_i
        }
        sigma = sigma.mod_floor(&n);

        Ok(Proof { mu: mu.to_string(), sigma: sigma.to_string() })
    }

    pub fn verify(
        &self,
        u: String,
        name: String,
        q_slice: Vec<QElement>,
        sigma: String,
        mu: String,
        _thread_num: usize,
    ) -> Result<bool, PDPError> {
        let n = num_bigint::BigUint::from_bytes_be(&self.pkey.n().to_bytes_be());
        let e = num_bigint::BigUint::from_bytes_be(&self.pkey.e().to_bytes_be());
        let mut multiply = 1.to_biguint().unwrap();
        let mut w = W::new();
        w.name = name;

        for q in q_slice {
            w.i = q.i;
            let w_hash = num_bigint::BigUint::from_bytes_be(&w.hash());
            let pow = w_hash.modpow(&num_bigint::BigUint::from_bytes_be(&q.v), &n);
            multiply *= pow;
        }
        let u = num_bigint::BigUint::from_str(&u)
            .map_err(|e| PDPError { error_code: FailCode::ParameterError(e.to_string()) })?;
        let mu = num_bigint::BigUint::from_str(&mu)
            .map_err(|e| PDPError { error_code: FailCode::ParameterError(e.to_string()) })?;
        let sigma = num_bigint::BigUint::from_str(&sigma)
            .map_err(|e| PDPError { error_code: FailCode::ParameterError(e.to_string()) })?;
        let u_pow_mu = u.modpow(&mu, &n);

        multiply *= u_pow_mu;
        multiply = multiply.mod_floor(&n);

        let sigma = sigma.modpow(&e, &n);
        Ok(sigma.cmp(&multiply).is_eq())
    }

    pub fn phi_record_compare_then_update_with_new_key(
        &self,
        old_phis_record:Vec<String>,
        miner_phis:Vec<String>,
    )->Result<Vec<String>,PDPError>{
        let d = num_bigint::BigUint::from_bytes_be(&self.skey.d().to_bytes_be());
        let n = num_bigint::BigUint::from_bytes_be(&self.skey.n().to_bytes_be());
        let e = num_bigint::BigUint::from_bytes_be(&self.skey.e().to_bytes_be());
        
        let mut index = 0;
        let mut new_phis_record_with_new_key = Vec::new();
        for i in old_phis_record{
            if !i == miner_phis[index].clone(){
                return Err(PDPError { error_code: FailCode::ParameterError(
                "The phis offer from miner is not same as such tee recorded before!".to_string()
                )})
            }
            let phi = BigUint::from_str(&i).unwrap();
            new_phis_record_with_new_key.push(phi.modpow(&e,&n).modpow(&d, &n).to_string())
        };
        Ok(new_phis_record_with_new_key)
    }

}
fn generate_sigma(
    ssk: RsaPrivateKey,
    data: Vec<u8>,
    name: String,
    i: u64,
    u_bigint: Arc<BigUint>,
) -> String {
    let d = num_bigint::BigUint::from_bytes_be(&ssk.d().to_bytes_be());
    let n = num_bigint::BigUint::from_bytes_be(&ssk.n().to_bytes_be());

    let mut w_i = W::new();
    w_i.i = i;
    w_i.name = name;

    //H(Wi)
    let w_i_hash = w_i.hash();
    let data_bigint = num_bigint::BigUint::from_bytes_be(&data);
    let w_i_hash_bigint = num_bigint::BigUint::from_bytes_be(&w_i_hash);

    //(H(Wi) · u^mi )^d
    let umi = u_bigint.modpow(&data_bigint, &n);

    let mut summary = w_i_hash_bigint * umi;
    summary = summary.mod_floor(&n);
    let productory = summary.modpow(&d, &n);

    productory.to_string()
}

pub fn tag_record(
    old_phis_record:Vec<String>,
    tag:Tag
) -> Result<Vec<String>,PDPError>{
    if old_phis_record.len()!=tag.t.phi.len() {
        return Err(PDPError { error_code: FailCode::ParameterError(format!(
            "the length of old_sigmas is not equal to phi :{:?}",
            e.to_string()
        )), })
    };

    let phis:Vec<BigUint> = old_phis_record.into_iter().map(|s| num_bigint::BigUint::from_str(&s).unwrap()).collect();

    let mut new_phis_record = Vec::new();
    let mut index = 0;
    for p in phis {
        let phi = num_bigint::BigUint::from_str(&tag.t.phi[index]).unwrap();
        new_phis_record.push((phi*p).to_string());
        index+=1;
    }
    Ok(new_phis_record)
}