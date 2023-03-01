use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use dryoc::constants;
use dryoc::generichash::{GenericHash, Key};
use dryoc::pwhash::{PwHash, Config};
use dryoc::types::{ByteArray, StackByteArray};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum SphinxError {
    #[error("assertion chal ∈ G^∗ failed")]
    InvalidRistretto255Point,
    #[error("assertion failed for scalar value")]
    InvalidRistretto255Scalar,
    #[error("DRYOC error")]
    DryocError(dryoc::Error),
}

impl From<dryoc::Error> for SphinxError {
    fn from(e: dryoc::Error) -> Self {
        SphinxError::DryocError(e)
    }
}

type MyRistrettoPoint = [u8; 32];
type MyRistrettoScalar = [u8; 32];
type Salt = [u8; constants::CRYPTO_PWHASH_SALTBYTES as usize];

type Challenge = MyRistrettoPoint;
type Response = MyRistrettoPoint;
type Rwd = Vec<u8>;
type BlindingFactor = Scalar;
type Secret = MyRistrettoScalar;

pub fn challenge(pwd: &[u8]) -> Result<(BlindingFactor, Challenge), SphinxError> {
    let h0: StackByteArray<64> = GenericHash::hash::<_, StackByteArray<0>, _>(&pwd, None)?;
    let H0 = RistrettoPoint::from_uniform_bytes(h0.as_array());
    let mut rng = rand::rngs::OsRng {};
    let bfac = Scalar::random(&mut rng);
    let chal = H0 * bfac;
    Ok((bfac, *chal.compress().as_bytes()))
}

pub fn respond(chal: Challenge, secret: Secret) -> Result<Response, SphinxError> {
    let point = CompressedRistretto::from_slice(&chal).decompress().ok_or(SphinxError::InvalidRistretto255Point)?;
    let scalar = Scalar::from_canonical_bytes(secret).ok_or(SphinxError::InvalidRistretto255Scalar)?;
    let product = point * scalar;
    Ok(*product.compress().as_bytes())
}

pub fn finish(pwd: &[u8], bfac: BlindingFactor, resp: Response, salt: Salt) -> Result<Rwd, SphinxError> {
    let rp = CompressedRistretto::from_slice(&resp).decompress().ok_or(SphinxError::InvalidRistretto255Point)?;
    let ir = bfac.invert();
    let H0_k = rp * ir;
    let mut hasher = GenericHash::new_with_defaults::<Key>(None)?;
    hasher.update(pwd);
    hasher.update(H0_k.compress().as_bytes());
    let rwd0: StackByteArray<32> = hasher.finalize()?;
    let rwd: PwHash<Rwd, Salt> = PwHash::hash_with_salt(&rwd0, salt, Config::interactive())?;
    Ok(rwd.into_parts().0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let pwd = b"shitty password";
        let salt = {
            let mut salt = [0u8; constants::CRYPTO_PWHASH_SALTBYTES as usize];
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
}
