use std::ops::{Add, Mul, Sub, Neg, AddAssign, MulAssign, SubAssign};
use rand::random;
use rayon::prelude::*;
use lazy_static::lazy_static;
use concrete_ntt::prime64::Plan;

use crate::poly::{DEGREE,Poly};
use crate::matrix::Matrix;

pub const P1: u64 = 137438960129;           // a 38 bits prime (the signature prime)
pub const P2: u64 = 33556993;               // a 27 bits prime
pub const P1_128: i128 = 137438960129;      
pub const P2_128: i128 = 33556993; 
pub const P1_U128: u128 = 137438960129; 

lazy_static! {
        pub static ref RING_P1: Plan = Plan::try_new(DEGREE, P1).unwrap(); 
        pub static ref RING_P2: Plan = Plan::try_new(DEGREE, P2).unwrap();
}

// struct for NTT representation in the ring Z/mZ[X] / (x^d + 1) where m = p1 * p2
#[derive(Debug, Clone, Default)]
pub struct CRT {
    pub a1: Vec<u64>,            // the NTT representation modulo p1
    pub a2: Vec<u64>,            // the NTT representation modulo p2
}

pub const MODULUS: i128 = 4612038222976132097;     // The 63 bits composite modulus
pub const MOD_SIZE: usize = 63;

pub const U1: i128 = -631677981968411998;
pub const U2: i128 = 631677981968411999;

impl CRT {
    pub fn zero() -> Self {
        Self { a1: vec![], a2: vec![] }
    }

    pub fn is_zero(&self) -> bool {
        if self.a1.len() == 0 && self.a2.len() == 0 {
            return true;
        }
        for i in 0..DEGREE {
            if self.a1[i] % P1 != 0 || self.a2[i] % P2 != 0 {
                return false;
            }
        }
        true
    }

    pub fn one() -> Self {
        Self {  a1: vec![1u64], a2: vec![1u64] }
    }

    pub fn constant(val: i128) -> Self {
        let mut v1 = val % P1_128; if v1 < 0 { v1 += P1_128; }
        let mut v2 = val % P2_128; if v2 < 0 { v2 += P2_128; }
        Self {  a1: vec![v1 as u64], a2: vec![v2 as u64] }
    }

    pub fn uniform() -> Self {
        Self {  a1: (0..DEGREE).map(|_| random::<u64>() % P1).collect(), 
                a2: (0..DEGREE).map(|_| random::<u64>() % P2).collect() }
    }

    pub fn as_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::new();
        for i in 0..DEGREE {
            bytes.extend_from_slice(&self.a1[i].to_be_bytes());
            bytes.extend_from_slice(&self.a2[i].to_be_bytes());
        }
        bytes
    }

    pub fn uniform_from_bytes(bytes: &Vec<[u8;8]>) -> Self {
        let mut a1 = vec![0u64; DEGREE];
        let mut a2 = vec![0u64; DEGREE];
        for i in 0..DEGREE {
            a1[i] = u64::from_le_bytes(bytes[2*i]) % P1;
            a2[i] = u64::from_le_bytes(bytes[2*i+1]) % P2;
        }
        Self { a1: a1, a2: a2 }
    }

    pub fn print(&self) {
        println!("{:?}", self.a1);
        println!("{:?}", self.a2);
    }
}

impl From<&Poly> for CRT {
    fn from(p: &Poly) -> Self {
        let mut p1 = vec![0; DEGREE]; let mut p2 = vec![0; DEGREE]; 
        for i in 0..DEGREE {
            let v = if p.coefs[i] < 0 { (p.coefs[i] + MODULUS) as u64 } else {p.coefs[i] as u64};
            p1[i] = v % P1; p2[i] = v % P2;
        }
        RING_P1.fwd(&mut p1);
        RING_P2.fwd(&mut p2);
        Self {  a1: p1.to_vec(), 
                a2: p2.to_vec(), }
    }
}

impl From<&CRT> for Poly {
    fn from(p: &CRT) -> Self {
        if p.a1.len() == 0 && p.a2.len() == 0 {
            return Poly::zero(MODULUS);
        }
        if p.a1.len() == 1 && p.a2.len() == 1 {
            let v = ((p.a1[0] as i128) * U2 +  (p.a2[0] as i128) * U1) % MODULUS;
            return Poly::constant(MODULUS, v);
        }
        let mut p1 = p.a1.clone();
        let mut p2 = p.a2.clone();
        RING_P1.normalize(&mut p1); RING_P1.inv(&mut p1);
        RING_P2.normalize(&mut p2); RING_P2.inv(&mut p2);

        let mut res = vec![0;DEGREE];
        for i in 0..DEGREE {
            res[i] = ((p1[i] as i128) * U2 + (p2[i] as i128) * U1) % MODULUS;
        }
        Self { modulus: MODULUS, coefs: res.to_vec() }
    }
}

impl PartialEq for CRT {
    fn eq(&self, other: &Self) -> bool {
        (self - other).is_zero()
    }
}

impl Add for &CRT {
    type Output = CRT;

    fn add(self, other: Self) -> CRT {
        let n = self.a1.len(); let m = other.a1.len();
        if n == 0 {
            return other.clone();
        }
        if m == 0 {
            return self.clone();
        }
        if n == 1 {
            return CRT {   
                a1: other.a1.iter().map(|v| (self.a1[0] + *v) % P1).collect(),
                a2: other.a2.iter().map(|v| (self.a2[0] + *v) % P2).collect(), };
        }
        if m == 1 {
            return CRT {   
                a1: self.a1.iter().map(|v| (other.a1[0] + *v) % P1).collect(),
                a2: self.a2.iter().map(|v| (other.a2[0] + *v) % P2).collect(), };
        }
        CRT {   a1: (0..DEGREE).map(|i| (self.a1[i] + other.a1[i]) % P1).collect(),
                a2: (0..DEGREE).map(|i| (self.a2[i] + other.a2[i]) % P2).collect() }
    }
}

impl Sub for &CRT {
    type Output = CRT;

    fn sub(self, other: Self) -> CRT {
        let n = self.a1.len(); let m = other.a1.len();
        if n == 0 {
            return -other;
        }
        if m == 0 {
            return self.clone();
        }
        if n == 1 {
            return CRT {   
                a1: other.a1.iter().map(|v| (self.a1[0] + P1 - *v) % P1).collect(),
                a2: other.a2.iter().map(|v| (self.a2[0] + P2 - *v) % P2).collect(), };
        }
        if m == 1 {
            return CRT {   
                a1: self.a1.iter().map(|v| (*v + P1 - other.a1[0]) % P1).collect(),
                a2: self.a2.iter().map(|v| (*v + P2 - other.a2[0]) % P2).collect(), };
        }
        CRT {   a1: (0..DEGREE).map(|i| (self.a1[i] + P1 - other.a1[i]) % P1).collect(),
                a2: (0..DEGREE).map(|i| (self.a2[i] + P2 - other.a2[i]) % P2).collect() }
    }
}

impl Neg for &CRT {
    type Output = CRT;

    fn neg(self) -> CRT {
        let n = self.a1.len();
        if n == 0 {
            return self.clone();
        }
        if n == 1 {
            return CRT {   
                a1: vec![P1 - self.a1[0]],
                a2: vec![P2 - self.a2[0]], };
        }
        CRT {   a1: self.a1.iter().map(|a| P1 - a).collect(),
                a2: self.a2.iter().map(|a| P2 - a).collect() }
    }
}

impl Mul for &CRT {
    type Output = CRT;

    fn mul(self, other: Self) -> CRT  {
        let n = self.a1.len(); let m = other.a1.len();
        if n == 0 || m == 0 {
            return CRT::zero();
        }
        if n == 1 {
            return CRT {   
                a1: other.a1.iter().map(|&v| (((self.a1[0] as u128) * (v as u128)) % P1_U128) as u64).collect(),
                a2: other.a2.iter().map(|&v| (self.a2[0] * v) % P2).collect(), };
        }
        if m == 1 {
            return CRT {   
                a1: self.a1.iter().map(|&v| (((v as u128) * (other.a1[0] as u128)) % P1_U128) as u64).collect(),
                a2: self.a2.iter().map(|&v| (v * other.a2[0]) % P2).collect(), };
        }
        let mut a1 = [0u64; DEGREE];
        let mut a2 = [0u64; DEGREE];
        RING_P1.mul_accumulate(&mut a1, &self.a1, &other.a1);
        RING_P2.mul_accumulate(&mut a2, &self.a2, &other.a2);
        CRT {   a1: a1.to_vec(),
                a2: a2.to_vec(), }
    }
}


impl Mul<u64> for &CRT {
    type Output = CRT;

    fn mul(self, other: u64) -> CRT {
        let n = self.a1.len(); 
        if other == 0 || n == 0 {
            return CRT::zero();
        }
        let v1 = other as u128 % P1_U128;
        let v2 = other % P2;
        if n == 1 {
            return CRT {   
                a1: vec![(v1 * (self.a1[0] as u128) % P1_U128) as  u64],
                a2: vec![v2 * self.a2[0] % P2], };
        }
        CRT {   a1: self.a1.iter().map(|&a| ((a as u128) * v1 % P1_U128) as u64).collect(),
                a2: self.a2.iter().map(|&a| a * v2 % P2).collect() }
    }
}

impl Mul<(u64,u64)> for &CRT {
    type Output = CRT;

    fn mul(self, other: (u64,u64)) -> CRT {
        let n = self.a1.len(); 
        if other == (0,0) || n == 0 {
            return CRT::zero();
        }
        if n == 1 {
            return CRT {   
                a1: vec![((other.0 as u128) * (self.a1[0] as u128) % P1_U128) as u64],
                a2: vec![other.1 * self.a2[0] % P2], };
        }
        CRT {   a1: self.a1.iter().map(|a| ((*a as u128) * (other.0 as u128) % P1_U128) as u64).collect(),
                a2: self.a2.iter().map(|a| a * other.1 % P2).collect() }
    }
}

// struct for polynomial operations in the ring Z/mZ[X] / (x^d + 1)
#[derive(Debug, Clone, PartialEq, Default)]
pub struct MatrixCRT {
    pub nb_rows: usize,
    pub nb_cols: usize,
    pub coefs: Vec<CRT>               // the coefficients of the polynomial
}

impl MatrixCRT {
    pub fn zero(rows: usize, cols: usize) -> Self {
        let coefs: Vec<CRT> = vec![CRT::zero(); cols * rows];
        Self {  nb_rows: rows,
                nb_cols: cols,
                coefs: coefs }
    }

    pub fn one(rows: usize, cols: usize) -> Self {
        let coefs: Vec<CRT> = vec![CRT::one(); cols * rows];
        Self {  nb_rows: rows,
                nb_cols: cols,
                coefs: coefs }
    }

    pub fn is_zero(&self) -> bool {
        for c in &self.coefs {
            if !c.is_zero() { return false; }
        }
        true
    }

    pub fn identity(rows: usize) -> Self {
        let mut coefs: Vec<CRT> = vec![CRT::zero(); rows * rows];
        for i in 0..rows {
            coefs[i * rows + i] = CRT::one();
        }
        Self {  nb_rows: rows,
                nb_cols: rows,
                coefs: coefs }
    }

    pub fn transpose(&self) -> Self {
        let mut t = vec![CRT::zero(); self.nb_rows * self.nb_cols];
        for i in 0..self.nb_rows {
            let ind = i * self.nb_cols;
            for j in 0..self.nb_cols {
                t[j * self.nb_rows + i] = self.coefs[ind + j].clone();
            }
        }
        Self { nb_rows: self.nb_cols,
               nb_cols: self.nb_rows,
               coefs: t }
    }

    pub fn uniform(rows: usize, cols: usize) -> MatrixCRT {
        let mut mat = MatrixCRT::zero(rows, cols);
        for i in 0..rows*cols {
            mat.coefs[i] = CRT::uniform();
        }
        MatrixCRT::from(mat)
    }

    pub fn gaussian(rows: usize, cols: usize, sigma: usize) -> Self {
        let nb = rows * cols;
        let mut coefs = Vec::with_capacity(nb);
        let result: Vec<CRT> = (0..nb)
            .into_par_iter()
            .map(|_| CRT::from(&Poly::gaussian(MODULUS, sigma)))
            .collect();  

        coefs.extend(result);
        Self {
            nb_rows: rows,
            nb_cols: cols,
            coefs: coefs.to_vec()
        }
    }

    pub fn concatenate(&mut self, mat: &MatrixCRT) {
        if self.nb_rows == 0 {
            self.nb_rows = mat.nb_rows;
            self.nb_cols = mat.nb_cols;
            self.coefs = mat.coefs.clone();
            return;
        }
        if mat.nb_rows == 0 {
            return;
        }
        if self.nb_rows != mat.nb_rows {
            panic!("cannot concatenate, different row numbers !");
        }
        let new_col = self.nb_cols + mat.nb_cols;
        for i in 0..self.nb_rows {
            let line = &mat.coefs[(i*mat.nb_cols)..((i+1)*mat.nb_cols)];
            self.coefs.splice((self.nb_cols + i*new_col)..(self.nb_cols + i*new_col), 
                line.iter().cloned());
        }
        self.nb_cols = new_col;
    }

    pub fn concatenate_vert(&mut self, mat: &MatrixCRT) {
        if self.nb_cols == 0 {
            self.nb_rows = mat.nb_rows;
            self.nb_cols = mat.nb_cols;
            self.coefs = mat.coefs.clone();
            return;
        }
        if mat.nb_cols == 0 {
            return;
        }
        if self.nb_cols != mat.nb_cols {
            panic!("Trying to concatenate a {} columns matrix with a {} columns matrix!", self.nb_cols, mat.nb_cols);
        }
        self.nb_rows += mat.nb_rows;
        self.coefs.extend_from_slice(&mat.coefs.as_slice());
    }

    pub fn concatenate_diag(&mut self, mat: &MatrixCRT) {
        let n = self.nb_cols;
        self.concatenate(&MatrixCRT::zero(self.nb_rows, mat.nb_cols));
        let mut temp = MatrixCRT::zero(mat.nb_rows, n);
        temp.concatenate(&mat);
        self.concatenate_vert(&temp);
    }

    pub fn concatenate_anti_diag(&self, mat: &MatrixCRT) -> MatrixCRT {
        let mut temp = MatrixCRT::zero(self.nb_rows, mat.nb_cols);
        temp.concatenate(&self);
        let mut temp2 = mat.clone();
        temp2.concatenate(&MatrixCRT::zero(mat.nb_rows, self.nb_cols));
        temp.concatenate_vert(&temp2);
        temp
    }

    pub fn resize(&self, 
        start_row: usize, start_col: usize, 
        new_rows: usize, new_cols: usize
    ) -> MatrixCRT {
        let mut temp = MatrixCRT::zero(new_rows, new_cols);
        for i in 0..new_rows {
            let start_old = (start_row+i) * self.nb_cols + start_col; 
            let start_new = i * new_cols;
            for j in 0..new_cols{
                temp.coefs[start_new + j] = self.coefs[start_old+j].clone();
            }
        }
        temp
    }

    pub fn replace(&mut self, 
        start_row: usize, start_col: usize, 
        from_row: usize, from_col: usize, nb_row: usize, nb_col: usize,
        sub: &MatrixCRT
    ) {
        for i in 0..nb_row {
            let start_old = (start_row+i) * self.nb_cols + start_col; 
            let start_new = (from_row+i) * sub.nb_cols + from_col;
            for j in 0..nb_col {
                self.coefs[start_old + j] = sub.coefs[start_new + j].clone();
            }
        }
    }

    pub fn replace_full(&mut self, 
        start_row: usize, start_col: usize, 
        sub: &MatrixCRT
    ) {
        for i in 0..sub.nb_rows {
            let start_old = (start_row+i)*self.nb_cols + start_col; 
            let start_new = i*sub.nb_cols;
            for j in 0..sub.nb_cols {
                self.coefs[start_old + j] = sub.coefs[start_new + j].clone();
            }
        }
    }

    pub fn sigma(&self) -> Self {
        let mut mat = self.clone();
        for i in 0..self.nb_cols*self.nb_rows {
            mat.coefs[i].a1.reverse();
            mat.coefs[i].a2.reverse();
        }
        mat
    }

    pub fn sigma_assign(&mut self) {
        for i in 0..self.nb_cols*self.nb_rows {
            self.coefs[i].a1.reverse();
            self.coefs[i].a2.reverse();
        }
    }

    pub fn mirror(&self) -> Self {
        let half = self.nb_cols/2; 
        let mut t = MatrixCRT::zero(self.nb_rows, self.nb_cols);
        for i in 0..self.nb_rows {
            let ind = i * self.nb_cols;
            let ind2 = ind + half;
            for j in 0..half {
                t.coefs[ind + j] = self.coefs[ind2 + j].clone();
                t.coefs[ind2 + j] = self.coefs[ind + j].clone();
            }
        }
        t
    }

    pub fn double_mirror(&self, a: usize, b: usize) -> Self {
        let mut t = MatrixCRT::zero(self.nb_rows, self.nb_cols);
        for i in 0..self.nb_rows {
            let ind = i * self.nb_cols;
            for j in 0..a {
                t.coefs[ind + j] = self.coefs[ind + j + a].clone();
                t.coefs[ind + j + a] = self.coefs[ind + j].clone();
            }
            for j in 0..b {
                t.coefs[ind + 2*a + j] = self.coefs[ind + 2*a + j + b].clone();
                t.coefs[ind + 2*a + j + b] = self.coefs[ind + 2*a + j].clone();
            }
        }
        t
    }
}

impl From<Vec<Vec<CRT>>> for MatrixCRT {
    fn from(coefs: Vec<Vec<CRT>>) -> Self {
        let row = coefs.len(); let col = coefs[0].len();
        let mut coef = Vec::new();
        for line in coefs {
            coef.extend(line);
        }
            Self {  nb_rows: row,
                    nb_cols: col,
                    coefs: coef }
        }
}

impl From<&MatrixCRT> for Matrix {
    fn from(coefs: &MatrixCRT) -> Self {
        if coefs.nb_rows == 0 || coefs.nb_cols == 0 {
            return Matrix::zero(MODULUS, 0, 0);
        }
        let nb = coefs.nb_rows*coefs.nb_cols;
        let mut m = vec![Poly::zero(MODULUS);nb];
        for i in 0..nb {
            m[i] = Poly::from(&coefs.coefs[i]);
        }
        Self {      modulus: MODULUS,
                    nb_rows: coefs.nb_rows,
                    nb_cols: coefs.nb_cols,
                    coefs: m }
    }
}

impl From<&Matrix> for MatrixCRT {
    fn from(coefs: &Matrix) -> Self {
        if coefs.nb_rows == 0 || coefs.nb_cols == 0 {
            return MatrixCRT::zero(0, 0);
        }
        let nb = coefs.nb_rows*coefs.nb_cols;
        let mut m = vec![CRT::zero(); nb];
        for i in 0..nb {
            m[i] = CRT::from(&coefs.coefs[i]);
        }
        Self {      nb_rows: coefs.nb_rows,
                    nb_cols: coefs.nb_cols,
                    coefs: m }
    }
}

impl Add for &MatrixCRT {
    type Output = MatrixCRT;

    fn add(self, other: Self) -> MatrixCRT {
        if self.nb_rows == 0 || self.nb_cols == 0 {
            return other.clone();
        }
        if other.nb_rows == 0 || other.nb_cols == 0 {
            return self.clone();
        }
        if (self.nb_cols != other.nb_cols) || (self.nb_rows != other.nb_rows) {
            panic!("Trying to add a {}x{} matrix with a {}x{} matrix !", self.nb_rows, self.nb_cols, other.nb_rows, other.nb_cols);
        }
        let mut sum = vec![CRT::zero(); self.nb_cols * self.nb_rows];
        for i in 0..self.nb_rows*self.nb_cols {
            sum[i] =  &self.coefs[i] + &other.coefs[i];
        }
        MatrixCRT { nb_rows: self.nb_rows,
               nb_cols: self.nb_cols,
               coefs: sum }
    }
}

impl Sub for &MatrixCRT {
    type Output = MatrixCRT;

    fn sub(self, other: Self) -> MatrixCRT {
        if (self.nb_cols != other.nb_cols) || (self.nb_rows != other.nb_rows) {
            panic!("Trying to sub a {}x{} matrix with a {}x{} matrix !", self.nb_rows, self.nb_cols, other.nb_rows, other.nb_cols);
        }
        if self.nb_rows == 0 || self.nb_cols == 0 {
            return -other;
        }
        if other.nb_rows == 0 || other.nb_cols == 0 {
            return self.clone();
        }
        let mut sum = vec![CRT::zero(); self.nb_cols * self.nb_rows];
        for j in 0..self.nb_rows*self.nb_cols {
            sum[j] =  &self.coefs[j] - &other.coefs[j];
        }
        MatrixCRT { nb_rows: self.nb_rows,
               nb_cols: self.nb_cols,
               coefs: sum }
    }
}

impl Neg for &MatrixCRT {
    type Output = MatrixCRT;

    fn neg(self) -> MatrixCRT {
        let mut sum = vec![CRT::zero(); self.nb_cols * self.nb_rows];
        for j in 0..self.nb_rows*self.nb_cols {
                sum[j] =  - &self.coefs[j];
        }
        MatrixCRT { nb_rows: self.nb_rows,
               nb_cols: self.nb_cols,
               coefs: sum }
    }
}

impl Mul for &MatrixCRT {
    type Output = MatrixCRT;

    fn mul(self, other: Self) -> MatrixCRT {
        if self.is_zero() || other.is_zero() {
            return MatrixCRT::zero(0, 0);
        }
        if self.nb_cols != other.nb_rows {
                panic!("cannot multiply! left matrix is {}x{} but right one is {}x{}", 
                self.nb_rows, self.nb_cols, 
                other.nb_rows, other.nb_cols
            );
        }
        let mut sum = vec![CRT::zero(); other.nb_cols * self.nb_rows];
        for row in 0..self.nb_rows {
            for col in 0..other.nb_cols {
                let mut temp = CRT::zero();
                for coef in 0..self.nb_cols {
                    temp += &(&self.coefs[row*self.nb_cols+coef] * &other.coefs[coef*other.nb_cols+col]);
                }
                sum[row*other.nb_cols+col] = temp;
            }
        }
        MatrixCRT { nb_rows: self.nb_rows,
               nb_cols: other.nb_cols, 
               coefs: sum }
    }
}

impl Mul<u64> for &MatrixCRT {
    type Output = MatrixCRT;

    fn mul(self, other: u64) -> MatrixCRT {
        let (a,b) = (other % P1, other % P2);
        let mut temp = MatrixCRT::zero(self.nb_rows, self.nb_cols);
        temp.coefs = self.coefs.iter().map(|v| v * (a,b)).collect();
        temp
    }
}

impl Mul<&CRT> for &MatrixCRT {
    type Output = MatrixCRT;

    fn mul(self, other: &CRT) -> MatrixCRT {
        MatrixCRT { nb_rows: self.nb_rows,
               nb_cols: self.nb_cols,
               coefs: self.coefs.iter().map(|v| v * other).collect() }
    }
}

#[derive(Debug, Clone, Default)]
pub struct QuadraticCRT {
    pub r2: MatrixCRT,
    pub r1: MatrixCRT,
    pub r0: CRT,
}

impl QuadraticCRT {
    pub fn new(r2: &MatrixCRT, r1: &MatrixCRT, r0: &CRT) -> Self {
        Self { 
            r2: r2.clone(),
            r1: r1.clone(),
            r0: r0.clone(),
        }
    }

    pub fn zero() -> Self {
        Self { 
            r2: MatrixCRT::zero(0,0),
            r1: MatrixCRT::zero(0,0),
            r0: CRT::zero(),
        }
    }

    pub fn from_scalar(r0: &CRT) -> Self {
        Self { 
            r2: MatrixCRT::zero(0, 0),
            r1: MatrixCRT::zero(0, 0),
            r0: r0.clone(),
        }
    }

    pub fn eval(&self, x: &MatrixCRT) -> CRT {
        let mut temp = &x.transpose() * &self.r2;
        temp += &self.r1;
        temp *= x;
        if temp.nb_rows == 0 || temp.nb_cols == 0 {
            return self.r0.clone();
        } 
        &temp.coefs[0] + &self.r0
    }


    pub fn projection(&self, proj: &MatrixCRT) -> Self {
        let temp = &self.r2 * proj;
        Self {
            r2: &proj.transpose() * &temp,
            r1: &self.r1 * proj,
            r0: self.r0.clone(),
        }
    }
}

impl Add for &QuadraticCRT {
    type Output = QuadraticCRT;

    fn add(self, other: Self) -> QuadraticCRT {
        QuadraticCRT { r2: &self.r2 + &other.r2,
                    r1: &self.r1 + &other.r1,
                    r0: &self.r0 + &other.r0,
        }
    }
}

impl Sub for &QuadraticCRT {
    type Output = QuadraticCRT;

    fn sub(self, other: Self) -> QuadraticCRT {
        QuadraticCRT { r2: &self.r2 - &other.r2,
                    r1: &self.r1 - &other.r1,
                    r0: &self.r0 - &other.r0,
        }
    }
}

impl Neg for QuadraticCRT {
    type Output = QuadraticCRT;

    fn neg(self) -> QuadraticCRT {
        QuadraticCRT { r2: -&self.r2,
                    r1: -&self.r1,
                    r0: -&self.r0,
        }
    }
}

impl Mul<&CRT> for &QuadraticCRT {
    type Output = QuadraticCRT;

    fn mul(self, other: &CRT) -> QuadraticCRT {
        QuadraticCRT { r2: &self.r2 * other,
                    r1: &self.r1 * other,
                    r0: &self.r0 * other,
        }
    }
}

impl Mul<u64> for &QuadraticCRT {
    type Output = QuadraticCRT;

    fn mul(self, other: u64) -> QuadraticCRT {
        QuadraticCRT { r2: &self.r2 * other,
                    r1: &self.r1 * other,
                    r0: &self.r0 * other,
        }
    }
}

impl AddAssign<&CRT> for CRT {
    fn add_assign(&mut self, other: &CRT) {
        let n = self.a1.len(); let m = other.a1.len();
        if n == 0 {
            *self = other.clone();
            return;
        }
        if m == 0 {
            return;
        }
        if n == 1 {
            self.a1 = other.a1.iter().map(|v| (self.a1[0] + *v) % P1).collect();
            self.a2 = other.a2.iter().map(|v| (self.a2[0] + *v) % P2).collect();
            return;
        }
        if m == 1 {
            self.a1 = self.a1.iter().map(|v| (other.a1[0] + *v) % P1).collect();
            self.a2 = self.a2.iter().map(|v| (other.a2[0] + *v) % P2).collect();
            return;
        }
        self.a1 = (0..DEGREE).map(|i| (self.a1[i] + other.a1[i]) % P1).collect();
        self.a2 = (0..DEGREE).map(|i| (self.a2[i] + other.a2[i]) % P2).collect();
    }
}

impl SubAssign<&CRT> for CRT {
    fn sub_assign(&mut self, other: &CRT) {
        let n = self.a1.len(); let m = other.a1.len();
        if n == 0 {
            *self = -other;
            return;
        }
        if m == 0 {
            return;
        }
        if n == 1 {
            self.a1 = other.a1.iter().map(|v| if *v > self.a1[0] { self.a1[0] + P1 - *v }
                else { self.a1[0] - *v }).collect();
            self.a2 = other.a2.iter().map(|v| if *v > self.a2[0] { self.a2[0] + P2 - *v }
                else { self.a2[0] - *v }).collect();
            return;
        }
        if m == 1 {
            self.a1 = self.a1.iter().map(|v| if other.a1[0] > *v { *v + P1 - other.a1[0] }
                else { *v - other.a1[0] }).collect();
            self.a2 = self.a2.iter().map(|v| if other.a2[0] > *v { *v + P2 - other.a2[0] }
                else { *v - other.a2[0] }).collect();
            return;
        }
        self.a1 = (0..DEGREE).map(|i| if self.a1[i] < other.a1[i] { self.a1[i] + P1 - other.a1[i] }
            else { self.a1[i] - other.a1[i] }).collect();
        self.a2 = (0..DEGREE).map(|i| if self.a2[i] < other.a2[i] { self.a2[i] + P2 - other.a2[i] }
            else { self.a2[i] - other.a2[i] }).collect();
    }
}

impl MulAssign<u64> for CRT {
    fn mul_assign(&mut self, other: u64) {
        let n = self.a1.len(); 
        if other == 0 || n == 0 {
            self.a1 = vec![];
            self.a2 = vec![];
            return;
        }
        let v1 = other as u128 % P1_U128;
        let v2 = other % P2;
        if n == 1 {
            self.a1 = vec![(v1 * (self.a1[0] as u128) % P1_U128) as u64];
            self.a2 = vec![v2 * self.a2[0] % P2];
            return;
        }
        self.a1 = (0..DEGREE).map(|i| (((self.a1[i] as u128) * v1) % P1_U128) as u64).collect();
        self.a2 = (0..DEGREE).map(|i| (self.a2[i] * v2) % P2).collect();
    }
}

impl MulAssign<(u64,u64)> for CRT {
    fn mul_assign(&mut self, other: (u64,u64)) {
        let n = self.a1.len();
        if other == (0,0) || n == 0 {
            self.a1 = vec![];
            self.a2 = vec![];
            return;
        }
        let v1 = other.0 as u128 % P1_U128;
        let v2 = other.1 % P2;
        if n == 1 {
            self.a1 = vec![(v1 * (self.a1[0] as u128) % P1_U128) as u64];
            self.a2 = vec![v2 * self.a2[0] % P2];
            return;
        }
        self.a1 = (0..DEGREE).map(|i| (((self.a1[i] as u128) * v1) % P1_U128) as  u64).collect();
        self.a2 = (0..DEGREE).map(|i| (self.a2[i] * v2) % P2).collect();
    }
}

impl MulAssign<&CRT> for CRT {
    fn mul_assign(&mut self, other: &CRT) {
        let n = self.a1.len(); let m = other.a1.len();
        if n == 0 || m == 0 {
            self.a1 = vec![];
            self.a2 = vec![];
            return;
        }
        if n == 1 {
            self.a1 = other.a1.iter().map(|v| (self.a1[0] * *v) % P1).collect();
            self.a2 = other.a2.iter().map(|v| (self.a2[0] * *v) % P2).collect();
            return;
        }
        if m == 1 {
            self.a1 = self.a1.iter().map(|v| (*v * other.a1[0]) % P1).collect();
            self.a2 = self.a2.iter().map(|v| (*v * other.a2[0]) % P2).collect();
            return;
        }
        let mut res1 = vec![0; DEGREE]; let mut res2 = vec![0; DEGREE];
        RING_P1.mul_accumulate(&mut res1, &self.a1, &other.a1);
        RING_P2.mul_accumulate(&mut res2, &self.a2, &other.a2);
        self.a1 = res1; self.a2 = res2;
    }
}

impl AddAssign<&MatrixCRT> for MatrixCRT {
    fn add_assign(&mut self, other: &MatrixCRT) {
        if self.nb_rows == 0 || self.nb_cols == 0 {
            *self = other.clone();
            return;
        }
        if self.nb_cols != other.nb_cols || self.nb_rows != other.nb_rows {
            panic!("Failed to add, wrong sizes: {}x{} with {},{}", self.nb_rows, self.nb_cols,
            other.nb_rows, other.nb_cols);
        }
        if other.nb_rows == 0 || other.nb_cols == 0 {
            return;
        }
        for j in 0..self.nb_rows*self.nb_cols {
                self.coefs[j] += &other.coefs[j];
        }
    }
}

impl SubAssign<&MatrixCRT> for MatrixCRT {
    fn sub_assign(&mut self, other: &MatrixCRT) {
        if self.nb_rows == 0 || self.nb_cols == 0 {
            *self = -other;
            return;
        }
        if other.nb_rows == 0 || other.nb_cols == 0 {
            return;
        }
        for j in 0..self.nb_rows*self.nb_cols {
                self.coefs[j] -= &other.coefs[j];
        }
    }
}

impl MulAssign<&MatrixCRT> for MatrixCRT {
    fn mul_assign(&mut self, other: &MatrixCRT) {
        if self.is_zero() || other.is_zero() {
            self.nb_rows = 0;
            self.nb_cols = 0;
            self.coefs = vec![];
            return;
        }
        if self.nb_cols != other.nb_rows {
            panic!("cannot multiply! the first matrix is {}x{} while the second is {}x{}", 
                self.nb_rows, self.nb_cols, 
                other.nb_rows, other.nb_cols
            );
        }
        let mut sum = vec![CRT::zero(); other.nb_cols * self.nb_rows];
        for row in 0..self.nb_rows {
            for col in 0..other.nb_cols {
                let mut temp = CRT::zero();
                for coef in 0..self.nb_cols {
                    temp += &(&self.coefs[row*self.nb_cols+coef] * &other.coefs[coef*other.nb_cols+col]);
                }
                sum[row*other.nb_cols+col] = temp;
            }
        }
        self.coefs = sum;
        self.nb_cols = other.nb_cols;
    }
}

impl MulAssign<&CRT> for MatrixCRT {
    fn mul_assign(&mut self, other: &CRT) {
        if other.is_zero() {
            self.nb_rows = 0;
            self.nb_cols = 0;
            self.coefs = vec![];
            return;
        }
        for i in 0..self.nb_rows*self.nb_cols {
                self.coefs[i] *= other;
        }
    }
}

impl MulAssign<u64> for MatrixCRT {
    fn mul_assign(&mut self, other: u64) {
        let (a, b) = (other % P1, other % P2);
        for i in 0..self.nb_rows*self.nb_cols {
                self.coefs[i] *= (a, b);
        }
    }
}

impl AddAssign<&QuadraticCRT> for QuadraticCRT {
    fn add_assign(&mut self, other: &QuadraticCRT) {
        self.r2 += &other.r2;
        self.r1 += &other.r1;
        self.r0 += &other.r0;
    }
}

impl MulAssign<u64> for QuadraticCRT {
    fn mul_assign(&mut self, other: u64) {
        self.r2 *= other;
        self.r1 *= other;
        self.r0 *= other;
    }
}

impl MulAssign<&CRT> for QuadraticCRT {
    fn mul_assign(&mut self, other: &CRT) {
        self.r2 *= other;
        self.r1 *= other;
        self.r0 *= other;
    }
}

