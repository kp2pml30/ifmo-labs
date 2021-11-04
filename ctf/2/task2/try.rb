reg = /flag|ctf/i
('a'..'z').each { |a|
	('a'..'z').each { |b|
		ans = `task2.exe #{a} #{b}`
		if reg =~ ans
			puts ans
			puts a
			puts b
		end
	}
}