use std::io::{self, BufRead};

fn main() {
	let stdin = io::stdin();
	let mut iterator = stdin.lock().lines();
	let mut line1 = iterator.next().unwrap().unwrap();
	let line2 = iterator.next().unwrap().unwrap();

	// let comp = line1 + "#" + line2;
	let sz0 = line1.len();
	line1.push_str("#");
	line1.push_str(&line2);
	let mut z = Vec::new();
	z.resize(line1.len(), 0);
	let mut l = 0;
	let mut r = 0;
	let n = line1.len();
	let s = line1.as_bytes();
	for i in 1..n {
		if i <= r {
			z[i] = std::cmp::min(r- i + 1, z[i - l]);
		}
		while i + z[i] < n && s[z[i]] == s[i + z[i]] {
			z[i] += 1
		}
		if i + z[i] - 1 > r {
			l = i;
			r = i + z[i] - 1;
		}
	}
	let mut ansl = 0;
	for i in 1..n {
		if z[i] == sz0 {
			ansl += 1;
		}
	}
	println!("{}", ansl);
	for i in 1..n {
		if z[i] == sz0 {
			print!("{} ", i - sz0);
		}
	}
}
