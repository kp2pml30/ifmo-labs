break *0x0000000000400864
commands
	silent
	printf "%c", $eax
	cont
end

run