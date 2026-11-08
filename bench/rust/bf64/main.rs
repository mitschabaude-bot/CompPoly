//! Matched scalar kernels using the unchanged native leanVM field implementation.
use primitives::field::{F64, F192, F192Unreduced};
use std::{hint::black_box, io::{self, BufRead, Write}, time::Instant};

fn sink(x: F192) -> u64 { x.c0 ^ x.c1 ^ x.c2 }
#[inline(never)]
fn unary_k(n: usize, a: u64, op: impl Fn(F64) -> F64) -> u64 {
    let mut x = F64(a);
    for _ in 0..n { x = op(F64(x.0 ^ 0x9e3779b97f4a7c15)); }
    x.0
}
#[inline(never)]
fn unary_e(n: usize, a: F192, op: impl Fn(F192) -> F192) -> u64 {
    let mut x = a;
    for _ in 0..n {
        x = op(x + F192::new(0x9e3779b97f4a7c15, 0x1122334455667788, 0x8000000000000001));
    }
    sink(x)
}
#[inline(never)]
fn dot<const REDUCED: bool>(a: &[F192], b: &[F192], first: u64) -> F192 {
    let mut total = F192Unreduced::ZERO;
    let mut reduced = F192::ZERO;
    for i in 0..64 {
        let mut lhs = a[i];
        if i == 0 { lhs.c0 = first; }
        if REDUCED { reduced += lhs * b[i]; }
        else { total ^= lhs.mul_unreduced(b[i]); }
    }
    if REDUCED { reduced } else { total.reduce() }
}
fn main() {
    let args: Vec<_> = std::env::args().collect();
    let op = &args[1];
    let n: usize = args[2].parse().unwrap();
    let a = black_box(0x0123456789abcdef);
    let b = black_box(0xfedcba9876543210);
    let ea = F192::new(a, b, a ^ b);
    let eb = F192::new(b, a, b ^ 0x1122334455667788);
    let da: Vec<_> = (0..64).map(|i| F192::new(a ^ i, b, a ^ b)).collect();
    let db: Vec<_> = (0..64).map(|i| F192::new(b ^ i, a, b ^ 0x1122334455667788)).collect();
    let mut line = String::new();
    println!("begin"); io::stdout().flush().unwrap();
    io::stdin().lock().read_line(&mut line).unwrap();
    let start = Instant::now();
    let result = match op.as_str() {
        "masked" => {
            let mut x = F64(a);
            for _ in 0..n { x *= F64(b); }
            x.0
        }
        "masked-throughput" => {
            let mut xs = [F64(a), F64(b), F64(a ^ 2), F64(b ^ 3), F64(a ^ 4),
                          F64(b ^ 5), F64(a ^ 6), F64(b ^ 7), F64(a ^ 8), F64(b ^ 9)];
            for _ in 0..n/40 {
                for _ in 0..4 {
                    let old = xs;
                    xs = core::array::from_fn(|i| old[i] * old[(i+1)%10]);
                }
            }
            xs.into_iter().fold(0, |acc, x| acc ^ x.0)
        }
        "ext3" => {
            let mut x = ea;
            for _ in 0..n { x *= eb; }
            sink(x)
        }
        "masked-square" => unary_k(n, a, F64::square),
        "masked-inverse" => unary_k(n, a, F64::inv),
        "masked-frobenius" => unary_k(n, a, |mut x| {
            for _ in 0..8 { x = x.square(); } x
        }),
        "ext-square" => unary_e(n, ea, F192::square),
        "mixed" => unary_e(n, ea, |x| x.mul_base(F64(b))),
        "ext-qfrobenius" => unary_e(n, ea, F192::frobenius),
        "ext-frobenius" => unary_e(n, ea, |mut x| {
            for _ in 0..64 { x = x.square(); } x
        }),
        "dot64" => {
            let mut x = a;
            for _ in 0..n/64 { x ^= sink(dot::<false>(&da, &db, x)); }
            x
        }
        "dot64-reduced" => {
            let mut x = a;
            for _ in 0..n/64 { x ^= sink(dot::<true>(&da, &db, x)); }
            x
        }
        _ => panic!("unknown operation"),
    };
    let result = black_box(result);
    println!("end {} {result}", start.elapsed().as_nanos());
    io::stdout().flush().unwrap();
    line.clear(); io::stdin().lock().read_line(&mut line).unwrap();
}
