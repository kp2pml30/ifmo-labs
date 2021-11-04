while line = gets
	if /.*randomness.elf->random.*= (?<num>[0-9]+)$/ =~ line
		num = Integer(num)
		puts("INPUT " + (num % 26 + 97).chr + " from random #{num}")
	else
		puts line
	end
end