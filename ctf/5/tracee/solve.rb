# [pid  7046] read(3,  <unfinished ...>
# [pid  7047] write(4, "PZWQMA^YYF_Sinnn\25K", 18 <unfinished ...>

s = "PZWQMA^YYF_Sinnn\25K"
puts (s.chars.map { |x| x.ord ^ 0x36 }).pack('c*')