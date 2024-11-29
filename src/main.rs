use rand::{Rng,RngCore,thread_rng};
use std::time::Instant;

use rust_deanonymisation::regev::Regev;
use rust_deanonymisation::secret_sharing::SecretSharing;
use rust_deanonymisation::poly::{DEGREE,Poly};
use rust_deanonymisation::signature::Sign;
use rust_deanonymisation::zkp::ZKP;
use rust_deanonymisation::protocol::Protocol;

fn main() { 
    // The proof modulus is 4612038222976132097 = modulus_sign * 33556993
    // which is a 63 bits modulus
    pub const MESSAGE_SIZE: usize = 32;                 // size of the signed message

    let modulus_enc: i128 = 3329;                       // encryption modulus
    let mod_size_enc: usize = 12;                       // size of the encryption modulus
    let modulus_sign: u64 = 137438960129;               // signature modulus
    let mod_size_sign: usize = 38;                      // size of the signature modulus
    let modulus_enc_inv: i128 = 3679655608358247777;    // the inverse of modulus_enc modulo the proof modulus
    let nb_members = 100;                               // The number of users that join the group
    let threshold = 75;                                 // The threshold for de-anonymization

    let bg_ok = Regev {    
        modulus: modulus_enc,
        mod_size: mod_size_enc,             
        pub_row: 4,             
        pub_col: 9, 
        m_size: 1,
    };

    let mut bg_msk = bg_ok.clone(); bg_msk.m_size = mod_size_enc;
    
    let signature = Sign {
        modulus: modulus_sign as i128,
        mod_size: mod_size_sign,
        sigma: 50,   
        pk_rows: 2,
        pk_cols: 3, 
    };

    let zkp = ZKP {
        chall_kappa: 2,                  
        chall_eta: 59,    
        lambda: 2,
        sigma_1: 10000,
        sigma_2: 5000,
        sigma_d: 8000,
        sigma_e: 7000,
        opening_len: 41,         
        rows_a1: 12,
        wit_len: bg_ok.pub_col + bg_msk.pub_col                                 // size of r1 + r2
            + 2 * (signature.pk_rows * mod_size_sign) + signature.pk_cols       // size of gsk_i
            + 1 + mod_size_enc,                                                 // size of id + bin(c2)
        m_len: 0,
    };

    // generate a random message
    let mut message = [0u8; MESSAGE_SIZE];
    rand::thread_rng().fill_bytes(&mut message);

    // Generate the group identities, i.e. binary polynomials of weight w = 4 
    let mut ids = Vec::new();
    'outer: for i in 0..DEGREE {
        for j in i+1..DEGREE {
            for k in j+1..DEGREE {
                for l in k+1..DEGREE {
                    let mut id = vec![0; DEGREE];
                    id[i] = 1; id[j] = 1; id[k] = 1; id[l] = 1;
                    ids.push(id);
                    if ids.len() == nb_members {
                        break 'outer
                    }
                }
            }
        }
    }
    // We sample the signer randomly between the members of the group
    let mut rng = thread_rng();
    let signer_id = rng.gen_range(0..threshold);

    let ss = SecretSharing { 
        modulus: modulus_enc,
        threshold: threshold 
    };

    let poc =  Protocol {
        enc_ok: bg_ok,
        enc_msk: bg_msk,
        enc_ok_inv: modulus_enc_inv,
        signature: signature,
        zkp: zkp,
        threshold: ss,
    };

    let mut start;  let mut end;
    start = Instant::now();
    let setup = poc.setup(); 
    end = Instant::now();
    println!("Computing the setup       {:?}", end.duration_since(start));

    let mut keys = Vec::new();
    start = Instant::now();
    for i in 0..threshold {
        keys.push(poc.join(&setup.gpk, &setup.isk, Poly::from((&ids[i], modulus_enc)), (i+1) as i128));
    }
    end = Instant::now();
    println!("Av. time to join          {:?}", end.duration_since(start)/(threshold as u32));

    start = Instant::now();
    let sign = poc.sign(&setup.gpk, &keys[signer_id], &message); 
    end = Instant::now();
    println!("Signing time              {:?}",end.duration_since(start));

    let mut tokens = Vec::new();
    start = Instant::now();
    for i in 0..threshold {
        tokens.push(poc.gen_token(&sign, &keys[i]));
    } 
    end = Instant::now();
    println!("Av. time for 1 token      {:?}", end.duration_since(start)/(threshold as u32));

    start = Instant::now();
    let check = poc.verif(&setup.gpk, &sign, &message);
    end = Instant::now();
    println!("Checking the signature    {:?}", end.duration_since(start));
    println!("Signature correct ?   {}", check);

    start = Instant::now();
    let open = poc.open(&setup.ok, &sign, &tokens);
    end = Instant::now();
    println!("Opening the signature     {:?}", end.duration_since(start));
    println!("Signer identified ?   {}", open == Poly::from((&ids[signer_id], modulus_enc)));
}
