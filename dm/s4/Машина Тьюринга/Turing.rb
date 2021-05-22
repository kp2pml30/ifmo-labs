lines = File.read(ARGV[0]).lines
lines[0...5].each { |l| puts l }

$allchars = " as single word"

def negateStr(str)
	return checkNegated str[1..] if str[0] == "~"
	return ($allchars - str.chars.sort!).join ''
end

def checkNegated(str)
	return str if str[0] != "~"
	return negateStr str[1..]
end

def goline(l)
	from, charsf, _, st, ct, dir = l.split
	raise "badline $#{l}$" if dir == nil
	# prev = charsf
	charsf = checkNegated(charsf)
	charsf.each_char { |cf|
		raise if cf == '?'
		puts "#{from} #{cf} -> #{st} #{if ct == '?' then cf else ct end} #{dir}"
	}
end

def decrement(suff, accept, reject)
	suff = "decrement#{suff}"
	goline "#{suff} 0 -> #{suff} 1 <"
	goline "#{suff} 1 -> #{accept} 0 ^"
	goline "#{suff} ~01 -> #{reject} ? >"
end

def skipAll(suff, accept, reject, chrs, dir, after)
	suff = "skipAll#{suff}"
	goline "#{suff} #{chrs} -> #{suff} ? #{dir}"
	goline "#{suff} ~#{chrs} -> #{accept} ? #{after}"
end


def copyNum(suff, accept, reject)
	suff = "copyNum#{suff}"
	goline "#{suff} 01 -> #{suff}_fetch ? ^"
	goline "#{suff}_fetch 0 -> #{suff}_carry'o ? > "
	goline "#{suff}_fetch 1 -> #{suff}_carry'i ? > "
	executeLines([
		"@[io",
		"#{suff}_carry'. 0 -> #{suff}_carry. o > ",
		"#{suff}_carry'. 1 -> #{suff}_carry. i > ",
		"#{suff}_carry'. ~01 -> #{suff}_carry. ? > ",
		"#{suff}_carry. ~_ -> #{suff}_carry. ? > ",
		"@]"
	].reverse)
	goline "#{suff}_carryi _ -> #{suff}_goback 1 <"
	goline "#{suff}_carryo _ -> #{suff}_goback 0 <"
	goline "#{suff}_goback ~_oi -> #{suff}_goback ? <"
	goline "#{suff}_goback _ -> #{accept} ? >"
	goline "#{suff}_goback o -> #{suff}_fetch 0 ^"
	goline "#{suff}_goback i -> #{suff}_fetch 1 ^"
end

def mkfunc(l)
	f, suff, finishacc, finishrej, additional = l.split
	# STDERR.puts "function #{f}#{suff}"
	begin
		eval("#{f}(\"#{suff}\", \"#{finishacc}\", \"#{finishrej}\" #{if additional == nil then "" else additional end})")
	rescue SyntaxError => se
		STDERR.puts "failed line :: #{l}"
		raise
	end
end

def executeLines(linesStack)
	while !linesStack.empty?
		l = linesStack.pop.strip
		next if l == "" || l == "\n" || l[0] == "#"

		if l[0..1] == "@["
			symb = l[2..-1]
			STDERR.puts "{#{l}} => {#{symb}}"
			copy = []
			while true
				ln = linesStack.pop
				break if ln[0..1] == "@]"
				copy.push ln
			end

			symb.each_char { |ch|
				c1 = copy.dup
				c1.map! { |s| s.gsub(/\./, ch) }
				executeLines c1
			}

			executeLines(linesStack) { |a|
				a.gsub!(Regexp.new "")
			}
			next
		end

		next $allchars = l[2..].chars.sort! if l[0..1] == '@@'
		next mkfunc l[1..] if l[0] == '@'
		goline l
	end
end

lines = lines[5..].reverse!
executeLines lines

puts "kp2pml30_generated_file _ -> extended_turing_machine _ ^"
