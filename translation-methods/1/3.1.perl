my $txt = do { local $/; <STDIN> };
 
$txt =~ s/^\s*\n//s;
$txt =~ s/\n\s*$/\n/s;
 
$txt =~ s/([ \t\r]*\n){2,}/\n\n/g;
 
for (split /^/, $txt) {
    s/^[ \t]+//;
    s/[ \t]+$//;
    s/[ \t][ \t]+/ /g;
    print;
}