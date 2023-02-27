use std::{ptr, ffi::c_void, mem::size_of};
use std::os::raw::{c_char, c_int, c_ulonglong};
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use dryoc::generichash::GenericHash;
use dryoc::types::{ByteArray, StackByteArray};
use thiserror::Error;
use halite_sys::{crypto_generichash, crypto_core_ristretto255_HASHBYTES, crypto_core_ristretto255_SCALARBYTES, crypto_core_ristretto255_BYTES, sodium_mlock, sodium_munlock, crypto_core_ristretto255_from_hash, crypto_core_ristretto255_scalar_random, crypto_scalarmult_ristretto255, crypto_pwhash_SALTBYTES, crypto_core_ristretto255_is_valid_point, crypto_core_ristretto255_scalar_invert, crypto_generichash_state, crypto_generichash_init, crypto_generichash_update, crypto_generichash_final, crypto_pwhash, crypto_pwhash_OPSLIMIT_INTERACTIVE, crypto_pwhash_MEMLIMIT_INTERACTIVE, crypto_pwhash_ALG_DEFAULT};

#[derive(Error, Debug)]
pub enum SphinxError {
    #[error("libsodium failed to lock memory")]
    SodiumMemoryLockError,
    #[error("libsodium failed scalar multiplication")]
    SodiumScalarMultError,
    #[error("libsodium failed scalar inversion")]
    SodiumScalarInvertError,
    #[error("libsodium failed password hashing")]
    SodiumPasswordHashError,
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

type MyRistrettoPoint = [u8; crypto_core_ristretto255_BYTES as usize];
type MyRistrettoScalar = [u8; crypto_core_ristretto255_SCALARBYTES as usize];
type Salt = [u8; crypto_pwhash_SALTBYTES as usize];

type Challenge = MyRistrettoPoint;
type Response = MyRistrettoPoint;
type Rwd = MyRistrettoPoint;
type BlindingFactor = MyRistrettoScalar;
type Secret = MyRistrettoScalar;

pub fn challenge(pwd: &[u8]) -> Result<(BlindingFactor, Challenge), SphinxError> {
    let h0: StackByteArray<64> = GenericHash::hash::<_, StackByteArray<0>, _>(&pwd, None)?;
    let H0 = RistrettoPoint::from_uniform_bytes(h0.as_array());
    let mut rng = rand::rngs::OsRng {};
    let bfac = Scalar::random(&mut rng);
    let chal = H0 * bfac;
    Ok((*bfac.as_bytes(), *chal.compress().as_bytes()))
}

pub fn respond(chal: Challenge, secret: Secret) -> Result<Response, SphinxError> {
    let point = CompressedRistretto::from_slice(&chal).decompress().ok_or(SphinxError::InvalidRistretto255Point)?;
    let scalar = Scalar::from_canonical_bytes(secret).ok_or(SphinxError::InvalidRistretto255Scalar)?;
    let product = point * scalar;
    Ok(*product.compress().as_bytes())
}

pub fn finish(pwd: &[u8], bfac: BlindingFactor, resp: Response, salt: Salt) -> Result<Rwd, SphinxError> {
    validate_ristretto255_point(resp)?;
    let mut ir = [0u8; crypto_core_ristretto255_SCALARBYTES as usize];
    unsafe {
        if sodium_mlock(ir.as_mut_ptr() as *mut c_void, ir.len()) == -1 {
            return Err(SphinxError::SodiumMemoryLockError)
        }
        if crypto_core_ristretto255_scalar_invert(ir.as_mut_ptr(), bfac.as_ptr()) != 0 {
            sodium_munlock(ir.as_mut_ptr() as *mut c_void, ir.len());
            return Err(SphinxError::SodiumScalarInvertError);
        }
    }
    let mut H0_k = [0u8; crypto_core_ristretto255_BYTES as usize];
    unsafe {
        if sodium_mlock(H0_k.as_mut_ptr() as *mut c_void, H0_k.len()) == -1 {
            sodium_munlock(ir.as_mut_ptr() as *mut c_void, ir.len());
            return Err(SphinxError::SodiumMemoryLockError);
        }
        if crypto_scalarmult_ristretto255(H0_k.as_mut_ptr(), ir.as_ptr(), resp.as_ptr()) != 0 {
            sodium_munlock(  ir.as_mut_ptr() as *mut c_void,   ir.len());
            sodium_munlock(H0_k.as_mut_ptr() as *mut c_void, H0_k.len());
            return Err(SphinxError::SodiumScalarMultError);
        }
        sodium_munlock(ir.as_mut_ptr() as *mut c_void, ir.len());
    }
    let mut state: crypto_generichash_state = crypto_generichash_state { opaque: [0u8; 384] };
    let state_mut_ptr = &mut state as *mut _ as *mut c_void;
    unsafe {
        if sodium_mlock(state_mut_ptr, size_of::<crypto_generichash_state>()) == -1 {
            sodium_munlock(H0_k.as_mut_ptr() as *mut c_void, H0_k.len());
            return Err(SphinxError::SodiumMemoryLockError);
        }
        crypto_generichash_init(&mut state as *mut _, ptr::null(), 0, crypto_core_ristretto255_BYTES as usize);
        crypto_generichash_update(&mut state as *mut _, pwd.as_ptr(), pwd.len() as u64);
        crypto_generichash_update(&mut state as *mut _, H0_k.as_ptr(), H0_k.len() as u64);
    }
    let mut rwd0 = [0u8; crypto_core_ristretto255_BYTES as usize];
    let mut rwd = [0u8; crypto_core_ristretto255_BYTES as usize];
    unsafe {
        if sodium_mlock(rwd0.as_mut_ptr() as *mut c_void, rwd0.len()) == -1 {
            sodium_munlock(H0_k.as_mut_ptr() as *mut c_void, H0_k.len());
            sodium_munlock(state_mut_ptr, size_of::<crypto_generichash_state>());
            return Err(SphinxError::SodiumMemoryLockError);
        }
        crypto_generichash_final(&mut state as *mut _, rwd0.as_mut_ptr(), rwd0.len());
        sodium_munlock(H0_k.as_mut_ptr() as *mut c_void, H0_k.len());
        sodium_munlock(state_mut_ptr, size_of::<crypto_generichash_state>());
        if crypto_pwhash(rwd.as_mut_ptr(), rwd.len() as u64, rwd0.as_ptr() as *mut c_char, rwd0.len() as u64, salt.as_ptr(), crypto_pwhash_OPSLIMIT_INTERACTIVE as c_ulonglong, crypto_pwhash_MEMLIMIT_INTERACTIVE as usize, crypto_pwhash_ALG_DEFAULT as c_int) != 0 {
            /* out of memory */
            sodium_munlock(rwd0.as_mut_ptr() as *mut c_void, rwd0.len());
            return Err(SphinxError::SodiumPasswordHashError);
        }
        sodium_munlock(rwd0.as_mut_ptr() as *mut c_void, rwd0.len());
    }
    Ok(rwd)
}

fn validate_ristretto255_point(point: MyRistrettoPoint) -> Result<(), SphinxError> {
    if unsafe { crypto_core_ristretto255_is_valid_point(point.as_ptr()) } != 1 {
        return Err(SphinxError::InvalidRistretto255Point);
    } else {
        return Ok(());
    }
}

fn scalarmult_ristretto255(n: MyRistrettoScalar, p: MyRistrettoPoint) -> Result<MyRistrettoPoint, SphinxError> {
    let mut result = [0u8; crypto_core_ristretto255_BYTES as usize];
    if unsafe { crypto_scalarmult_ristretto255(result.as_mut_ptr(), n.as_ptr(), p.as_ptr()) } == 0 {
        Ok(result)
    } else {
        Err(SphinxError::SodiumScalarMultError)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let pwd = b"shitty password";
        let salt = {
            let mut salt = [0u8; crypto_pwhash_SALTBYTES as usize];
            salt[0] = 1;
            salt
        };
        let secret = {
            let mut secret = [0u8; crypto_core_ristretto255_SCALARBYTES as usize];
            secret[0] = 1;
            secret
        };
        let (bfac, chal) = challenge(pwd).unwrap();
        let resp = respond(chal, secret).unwrap();
        let rwd = finish(pwd, bfac, resp, salt).unwrap();
        println!("{}", hex::encode(rwd));
    }
}
