k = "st_3phr_b13gcsvut_3yf1rz{55}".freeze
(2..64).each { |n|
	a = ['?'] * n
	ki = 0
	7.times { |i|
		j = i
		while j < n
			a[j] = k[ki]
			ki += 1
			j += 7
		end
	}
	a.each { |c| print c }
	puts
}
# hmmmm spbctf{th1s_15_r3v3r53_guyz}