tasks = File.read 'tasks.txt'

taskDescr = {}

tasks.lines.map { |t|
	m = /^(?<digs>\d+\.\d+\.\d+): (?<rest>.*)/.match t
	raise "bad line #{t}" if m == nil
	taskDescr[m[:digs]] = m[:rest].chop
}

raise 'Expected `input`' if ARGV.size != 1

inf = ARGV[0]

inp = File.read ARGV[0]

l = inp.lines.map { |l|
	l = l.strip
	m = /^(?<beg>.*ДЗ-)(?<digs>\d+\.\d+\.\d+)(?<end>.*)$/.match(l)
	if m != nil
		r = taskDescr[m[:digs]]
		fail if r == nil
		"#{m[:beg]}#{m[:digs]}. #{r}#{m[:end]}"
	else
		l
	end
}

def divide_text(str, n)
	ret = []
	while str != ''
		str.lstrip!
		s = str[/^.{,#{n}}(?=\s|$)/] || str
		ret.push s
		str = str[s.size..-1]
	end
	return ret
end

l = l.flat_map { |l|
	next [l] if l.size <= 60
	m = /^--(?<ident>\s*)(?<rest>.*)$/.match l
	next [l] if m == nil
	l = divide_text(m[:rest], 60)
	f = -1
	l.map { |l|
		f += 1
		"--#{m[:ident]}#{f > 0 ? '  ' : ''}#{l}"
	}
}

s = l.join("\n")

# puts s

File.write "#{File.dirname(inf)}/#{File.basename(inf,'.txt')}.out.txt", s