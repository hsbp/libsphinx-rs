use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use dryoc::classic::crypto_generichash::crypto_generichash;
use dryoc::constants::{CRYPTO_PWHASH_SALTBYTES, CRYPTO_GENERICHASH_BLAKE2B_BYTES};
use dryoc::generichash::{GenericHash, Key};
use dryoc::pwhash::{Config, PwHash};
use dryoc::types::{ByteArray, StackByteArray};
use thiserror::Error;
use vararg::vararg;
use std::cmp::Ordering;
use std::io::Cursor;
use byteorder::{BigEndian, LittleEndian, ReadBytesExt, WriteBytesExt};
use strum_macros::IntoStaticStr;
use blake2b_simd::{blake2b, Params};

#[derive(Error, Debug)]
pub enum SphinxError {
    #[error("assertion chal ∈ G^∗ failed")]
    InvalidRistretto255Point,
    #[error("assertion failed for scalar value")]
    InvalidRistretto255Scalar,
    #[error("DRYOC error")]
    DryocError(dryoc::Error),
}

#[derive(Error, Debug)]
pub enum EquihashError {
    #[error("invalid proof length for given solution size")]
    InvalidLength,
    #[error("invalid proof")]
    InvalidProof,
    #[error("no proof found below MAX_NONCE")]
    NoProofFound,
}

impl From<dryoc::Error> for SphinxError {
    fn from(e: dryoc::Error) -> Self {
        SphinxError::DryocError(e)
    }
}

type MyRistrettoPoint = [u8; 32];
type MyRistrettoScalar = [u8; 32];
type Salt = [u8; CRYPTO_PWHASH_SALTBYTES];

type Challenge = MyRistrettoPoint;
type Response = MyRistrettoPoint;
type Rwd = Vec<u8>;
type BlindingFactor = Scalar;
type Secret = MyRistrettoScalar;

pub fn challenge(pwd: &[u8]) -> Result<(BlindingFactor, Challenge), SphinxError> {
    let h0: StackByteArray<64> = GenericHash::hash::<_, StackByteArray<0>, _>(&pwd, None)?;
    let mut rng = rand::rngs::OsRng {};
    let bfac = Scalar::random(&mut rng);
    let chal = RistrettoPoint::from_uniform_bytes(h0.as_array()) * bfac;
    Ok((bfac, *chal.compress().as_bytes()))
}

pub fn respond(chal: Challenge, secret: Secret) -> Result<Response, SphinxError> {
    let point = CompressedRistretto::from_slice(&chal)
        .decompress()
        .ok_or(SphinxError::InvalidRistretto255Point)?;
    let scalar =
        Scalar::from_canonical_bytes(secret).ok_or(SphinxError::InvalidRistretto255Scalar)?;
    let product = point * scalar;
    Ok(*product.compress().as_bytes())
}

pub fn finish(
    pwd: &[u8],
    bfac: BlindingFactor,
    resp: Response,
    salt: Salt,
) -> Result<Rwd, SphinxError> {
    let rp = CompressedRistretto::from_slice(&resp)
        .decompress()
        .ok_or(SphinxError::InvalidRistretto255Point)?;
    let ir = bfac.invert();
    let mut hasher = GenericHash::new_with_defaults::<Key>(None)?;
    hasher.update(pwd);
    hasher.update((rp * ir).compress().as_bytes());
    let rwd0: StackByteArray<32> = hasher.finalize()?;
    let rwd: PwHash<Rwd, Salt> = PwHash::hash_with_salt(&rwd0, salt, Config::interactive())?;
    Ok(rwd.into_parts().0)
}

#[derive(Debug)]
pub struct Equihash {
    n: usize,
    k: usize,
    seed: Vec<u8>,
}

#[derive(Debug)]
pub struct Solver<'a> {
    parent: &'a Equihash,
    nonce: u32,
    tuple_list: Vec<[Tuple ; LIST_LENGTH]>,
    filled_list: Vec<usize>,
    solutions: Vec<Proof>,
    forks: Vec<Vec<Fork>>,
}

#[derive(Debug, Default, Clone)]
pub struct Tuple {
    blocks: Vec<u32>,
    reference: usize,
}

type Fork = (usize, usize);

impl<'a> Solver<'a> {
    fn fill_memory(&mut self, length: u32) {
        let seed_end_off = self.parent.seed.len() + 4;
        let mut input: Vec<u8> = self.parent.seed.clone();
        input.write_u32::<LittleEndian>(self.nonce).unwrap();
        input.write_u32::<LittleEndian>(0).unwrap();
        let mut buf = [0u8; CRYPTO_GENERICHASH_BLAKE2B_BYTES];
        for item in 0..length {
            let elem = item.to_le_bytes();
            for (j, b) in elem.iter().enumerate() {
                input[seed_end_off + j] = *b;
            }
            crypto_generichash(&mut buf, &input, None).unwrap();
            let mut rdr = Cursor::new(buf);
            let first_u32 = rdr.read_u32::<LittleEndian>().unwrap();
            let index = (first_u32 >> (32 - self.parent.n / (self.parent.k + 1))) as usize;
            let count = self.filled_list[index];
            if count < LIST_LENGTH {
                for j in 1..=self.parent.k {
                    let next_u32 = rdr.read_u32::<LittleEndian>().unwrap();
                    self.tuple_list[index][count].blocks[j - 1] = next_u32 >> (32 -
                        self.parent.n / (self.parent.k + 1));
                }
                self.tuple_list[index][count].reference = item as usize;
                self.filled_list[index] += 1;
            }
        }
    }

    fn resolve_tree(&self, fork: Fork) -> Vec<u32> {
        self.resolve_tree_by_level(fork, self.forks.len())
    }

    fn resolve_tree_by_level(&self, fork: Fork, level: usize) -> Vec<u32> {
        if level == 0 {
            return vec![fork.0 as u32, fork.1 as u32];
        }
        let mut v1 = self.resolve_tree_by_level(self.forks[level - 1][fork.0], level - 1);
        let mut v2 = self.resolve_tree_by_level(self.forks[level - 1][fork.1], level - 1);
        v1.append(&mut v2);
        v1
    }

    fn resolve_collissions(&mut self, store: bool) {
        let table_len = self.tuple_list.len();
        let max_new_collissions = table_len * FORK_MULTIPLIER;
        let new_blocks = self.tuple_list[0][0].blocks.len() - 1;
        let mut new_forks: Vec<Fork> = Vec::with_capacity(max_new_collissions);
        let mut collission_list: Vec<[Tuple ; LIST_LENGTH]> = vec![std::array::from_fn(|_| Tuple { blocks: vec![0u32; new_blocks], ..Default::default() }); table_len];
        let mut new_filled_list = vec![0usize; table_len];
        for (filled_list_elem, tuple_list_i) in self.filled_list.iter().zip(self.tuple_list.iter()) {
            let slice = &tuple_list_i[0..*filled_list_elem];
            let mut iter = slice.iter();
            while let Some(tl1) = iter.next() {
                for tl2 in iter.as_slice() {
                    let new_index = (tl1.blocks[0] ^ tl2.blocks[0]) as usize;
                    let new_fork = (tl1.reference, tl2.reference);
                    if store {
                        if new_index == 0 {
                            let solution_inputs: Vec<u32> = self.resolve_tree(new_fork);
                            let n = self.parent.n;
                            let k = self.parent.k;
                            self.solutions.push(Proof { n, k, seed: self.parent.seed.clone(), nonce: self.nonce, inputs: solution_inputs, digitbits: n / (k + 1) });
                        }
                    } else if new_filled_list[new_index] < LIST_LENGTH && new_forks.len() < max_new_collissions {
                        let mut tuple = &mut collission_list[new_index][new_filled_list[new_index]];
                        for l in 0..new_blocks {
                            tuple.blocks[l] = tl1.blocks[l + 1] ^ tl2.blocks[l + 1];
                        }
                        tuple.reference = new_forks.len();
                        new_forks.push(new_fork);
                        new_filled_list[new_index] += 1;
                    }
                }
            }
        }
        self.forks.push(new_forks);
        self.tuple_list = collission_list;
        self.filled_list = new_filled_list;
    }
}

impl Equihash {
    fn find_proof(&self) -> Result<Proof, EquihashError> {
        let mut nonce = 1;
        while nonce < MAX_NONCE {
            nonce += 1;
            let mut solver = self.init_memory(nonce);
            solver.fill_memory(4 << (self.n / (self.k + 1) - 1));
            for i in 1..=self.k {
                let to_store = i == self.k;
                solver.resolve_collissions(to_store);
            }
            for solution in solver.solutions {
                let mut vec = solution.inputs.clone();
                vec.sort();
                if vec.windows(2).all(|s| s[0] != s[1]) {
                    return Ok(solution);
                }
            }
        }
        Err(EquihashError::NoProofFound)
    }

    fn init_memory(&self, nonce: u32) -> Solver {
        let tuple_n = 1 << (self.n / (self.k + 1));
        let tuple_list: Vec<[Tuple ; LIST_LENGTH]> = vec![std::array::from_fn(|_| Tuple { blocks: vec![0u32; self.k], ..Default::default() }); tuple_n];
        let filled_list = vec![0usize; tuple_n];
        Solver { tuple_list, filled_list, solutions: vec![], forks: vec![], parent: self, nonce }
    }
}

#[derive(Debug)]
pub struct Proof {
    n: usize,
    k: usize,
    seed: Vec<u8>,
    nonce: u32,
    inputs: Vec<u32>,
    digitbits: usize,
}

const MAX_NONCE: u32 = 0xFFFFF;
const LIST_LENGTH: usize = 5;
const FORK_MULTIPLIER: usize = 3;

impl Proof {
    fn serialize(self: &Proof) -> Vec<u8> {
        let mut result = self.nonce.to_be_bytes().to_vec();
        let mut i = 0;
        let mut bits_left = self.digitbits + 1;
        let solsize = self.inputs.len() * (self.digitbits + 1) / 8;

        for _ in 0..solsize {
            let b = if bits_left >= 8 {
                bits_left -= 8;
                self.inputs[i] >> bits_left
            } else {
                let remaining = self.inputs[i] << (8 - bits_left);
                bits_left += self.digitbits + 1 - 8;
                i += 1;
                remaining | self.inputs[i] >> bits_left
            };
            result.push(b as u8);
        }
        result
    }

    fn verify(self: &Proof) -> Result<(), EquihashError> {
        let seed_end_off = self.seed.len() + 4;
        let mut input: Vec<u8> = self.seed.clone();
        input.write_u32::<LittleEndian>(self.nonce).unwrap();
        input.write_u32::<LittleEndian>(0).unwrap();
        let mut buf = [0u8; CRYPTO_GENERICHASH_BLAKE2B_BYTES];
        let mut blocks = vec![0u32; self.k + 1];
        for item in &self.inputs {
            let elem = item.to_le_bytes();
            for (j, b) in elem.iter().enumerate() {
                input[seed_end_off + j] = *b;
            }
            crypto_generichash(&mut buf, &input, None).unwrap();
            let mut rdr = Cursor::new(buf);
            for block in &mut blocks {
                *block ^= rdr.read_u32::<LittleEndian>().unwrap() >> (32 - self.n / (self.k + 1));
            }
        }
        if blocks.iter().all(|i| *i == 0) { Ok(()) } else { Err(EquihashError::InvalidProof) }
    }
}

pub fn deserialize_equihash(n: usize, k: usize, seed: Vec<u8>, serialized: &[u8]) -> Result<Proof, EquihashError> {
    let digitbits = n / (k + 1);
    let proofsize = (1 << k) as usize;
    let solsize = proofsize * (digitbits + 1) / 8;
    if solsize + 4 != serialized.len() {
        return Err(EquihashError::InvalidLength);
    }

    let mut rdr = Cursor::new(serialized);
    let nonce = rdr.read_u32::<BigEndian>().unwrap();
    let mut sol = vec![0u32; proofsize];
    let mut bits_left = digitbits + 1;
    let mut j = 0;

    while let Ok(result) = rdr.read_u8() {
        let next_byte = result as u32;
        match bits_left.cmp(&8) {
            Ordering::Greater => {
                sol[j] <<= 8;
                bits_left -= 8;
                sol[j] |= next_byte;
            },
            Ordering::Equal => {
                sol[j] <<= 8;
                sol[j] |= next_byte;
                bits_left = digitbits + 1;
                j += 1;
            },
            Ordering::Less => {
                sol[j] <<= bits_left;
                sol[j] |= (next_byte >> (8 - bits_left)) & ((1 << bits_left) - 1);
                j += 1;
                sol[j] = next_byte & ((1 << (8 - bits_left)) - 1);
                bits_left = (digitbits + 1) - (8 - bits_left);
            },
        }
    }

    Ok(Proof { n, k, seed, nonce, inputs: sol, digitbits })
}

#[derive(Eq, PartialEq, IntoStaticStr, Copy, Clone)]
enum DerivationContext {
    #[strum(serialize = "sphinx password context")]
    Password,
    #[strum(serialize = "sphinx host salt")]
    Salt,
    #[strum(serialize = "sphinx check digit context")]
    CheckDigit,
    #[strum(serialize = "sphinx signing key")]
    Signing,
    #[strum(serialize = "sphinx encryption key")]
    Encryption,
}

#[vararg]
fn derive<const L: usize>(context: DerivationContext, inputs: [&[u8]; L]) -> Vec<u8> {
    let init: &str = context.into();
    let bytes = init.as_bytes().to_vec();
    let length = if context == DerivationContext::CheckDigit { 1 } else { CRYPTO_GENERICHASH_BLAKE2B_BYTES };
    inputs.iter().fold(bytes, |acc, msg| Params::new()
        .hash_length(length)
        .key(msg)
        .to_state()
        .update(&acc)
        .finalize()
        .as_bytes()
        .to_vec())
}

fn calculate_check_digit(rwd: &[u8]) -> u8 {
    let output = derive!(DerivationContext::CheckDigit, rwd);
    output[0]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let pwd = b"shitty password";
        let salt = {
            let mut salt = [0u8; CRYPTO_PWHASH_SALTBYTES];
            salt[0] = 1;
            salt
        };
        let secret = {
            let mut secret = [0u8; 32];
            secret[0] = 1;
            secret
        };
        let (bfac, chal) = challenge(pwd).unwrap();
        let resp = respond(chal, secret).unwrap();
        let rwd = finish(pwd, bfac, resp, salt).unwrap();
        println!("{}", hex::encode(rwd));
    }

    #[test]
    fn equihash() {
        let n = 40;
        let k = 4;
        let serialized = hex::decode("0000000352d0d30b884dfed5d647fe55eb55f4e06ed2").unwrap();
        let input = b"0123456789abcdef";
        let proof = deserialize_equihash(n, k, input.to_vec(), &serialized).unwrap();
        proof.verify().unwrap();
        let reserialized = proof.serialize();
        assert_eq!(reserialized, serialized);
        let eq = Equihash { n: 40, k: 4, seed: input.to_vec() };
        let our_proof = eq.find_proof().unwrap();
        our_proof.verify().unwrap();
        assert_eq!(our_proof.serialize(), serialized);
    }

    #[test]
    fn check_digit() {
        assert_eq!(calculate_check_digit(b"bar"), 0x86u8);
    }
}
