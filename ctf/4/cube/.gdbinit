define myprint
	set $i_row=0
	while $i_row <= 3
		set $i_col=0
		while $i_col <= 3
			set $i_cel=0
			if $i_row == $i_col && ($i_cel == 0 || $i_cel == 3 || $i_row == 0 || $i_row == 3)
				print (char)(char)(((100 * $i_row + 10 * $i_col) % 255) ^ ((char*)flag)[100 * $i_row + 10 * $i_col])
			end
			while $i_cel <= 2
				set $i_cel=$i_cel+1
				if $i_row == $i_col && ($i_cel == 0 || $i_cel == 3 || $i_row == 0 || $i_row == 3)
					print (char)((char)((100 * $i_row + 10 * $i_col + $i_cel) % 255) ^ ((char*)flag)[100 * $i_row + 10 * $i_col + $i_cel])
				end
			end
			set $i_col=$i_col+1
		end
		set $i_row=$i_row+1
	end
end

break *0x0
run

# execute by hand:
myprint
