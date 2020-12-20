a = gets

def prefix(s)
	p = [-1]
	(1..s.size).each { |i|
		if s[i - 1] == "#"
			p.push 0
			next
		end
		k = p[i - 1]
		while k >= 0
			if s[k] == s[i - 1]
				break
			end
			k = p[k]
		end
		p.push k + 1
	}
	return p
end

p = prefix(a)
p[1...-1].each { |i|
	print i
	print ' '
}

=begin
puts "-" + b + "#" + a
p = prefix(b + "#" + a)
puts p.inspect
a.size.times { |i|
	if p[i + b.size + 1 + 1] == b.size
		puts i - b.size + 1
	end
}
=end

