//! Read-only harness for the pinned leanVM encoder. Production arithmetic is a path dependency.
use pcs::ntt::{AdditiveNttF64, Codeword, Keep};
use primitives::field::F64;
use std::{hint::black_box, io::{self, Write, BufRead}, time::Instant};

fn seed(i: usize) -> F64 {
    F64(0x0123456789abcdef ^ (i as u64 + 1).wrapping_mul(0x9e3779b97f4a7c15))
}
fn digest(data: &[F64]) -> (u64,u64) {
    data.iter().fold((0xcbf29ce484222325, 0x84222325cbf29ce4), |(a,b), x| {
        ((a ^ x.0).wrapping_mul(0x100000001b3), b.rotate_left(7).wrapping_add(x.0))
    })
}
fn report(label: &str, data: &[F64]) {
    let (a,b) = digest(data);
    println!("{label} {} {a} {b}", data.len());
}
fn main() {
    let args: Vec<_> = std::env::args().collect();
    let (mode, layout) = (&args[1], &args[2]);
    let d: usize = args[3].parse().unwrap();
    let live: usize = args[4].parse().unwrap();
    let rate: usize = args[5].parse().unwrap();
    let lanes = if layout == "k" { live.next_multiple_of(8) } else { 3 * live };
    let rows = 1usize << d;
    let msg_rows = rows >> rate;
    let setup_start = Instant::now();
    let ntt = AdditiveNttF64::standard(d);
    let setup_ns = setup_start.elapsed().as_nanos();
    let message: Vec<_> = (0..msg_rows * if layout == "k" { live } else { lanes }).map(seed).collect();
    if mode == "bench" {
        println!("begin {setup_ns}"); io::stdout().flush().unwrap();
        let mut line = String::new(); io::stdin().lock().read_line(&mut line).unwrap();
        let start = Instant::now();
        let result = if layout == "k" {
            ntt.encode_lane_major(black_box(&message), live, lanes, rate, Keep::Whole, &|_,_| {})
        } else {
            ntt.encode_interleaved_with(black_box(&message), lanes, rate, false, &|_,_| {})
        };
        let elapsed = start.elapsed().as_nanos();
        let Codeword::Whole(data, _) = result else { panic!("whole codeword requested") };
        println!("end {elapsed}"); io::stdout().flush().unwrap();
        line.clear(); io::stdin().lock().read_line(&mut line).unwrap();
        let (a,b) = digest(black_box(&data));
        println!("sink {a}:{b}"); io::stdout().flush().unwrap();
        return;
    }
    // Scalar stage oracle: same twiddle and F64 arithmetic as the production encoder.
    let mut data = vec![F64::ZERO; rows * lanes];
    for row in 0..rows {
        for lane in 0..lanes {
            data[row * lanes + lane] = if layout == "k" {
                if lane < lanes - live { F64::ZERO }
                else { message[(lanes - 1 - lane) * msg_rows + row % msg_rows] }
            } else { message[(row % msg_rows) * lanes + lane] };
        }
    }
    report("input", &data);
    for layer in rate..d {
        let half = 1usize << (d-layer-1);
        for block in 0..1usize << layer {
            let t = ntt.twiddle(layer, block);
            for row in block*2*half..block*2*half+half {
                for lane in 0..lanes {
                    let (lo,hi) = (row*lanes+lane,(row+half)*lanes+lane);
                    let u = data[lo] + data[hi]*t;
                    data[hi] += u;
                    data[lo] = u;
                }
            }
        }
        report(&format!("stage-{}", d-layer-1), &data);
    }
    let production = if layout == "k" {
        ntt.encode_lane_major(&message, live, lanes, rate, Keep::Whole, &|_,_| {})
    } else {
        ntt.encode_interleaved_with(&message, lanes, rate, false, &|_,_| {})
    };
    let Codeword::Whole(got,_) = production else { panic!("whole codeword requested") };
    assert_eq!(data,got,"scalar stages disagree with production encoder");
    report("output", &got);
    if args.len() == 7 {
        let mut out = std::io::BufWriter::new(std::fs::File::create(&args[6]).unwrap());
        for x in &got { out.write_all(&x.0.to_le_bytes()).unwrap(); }
    }
}
