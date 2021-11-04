s = 120.chr
i = 5
while i > 0
	s << (s[-1].ord - i).chr
	i -= 1
end
puts s.reverse