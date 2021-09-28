# does NOT work

my $txt = do { local $/; <STDIN> };

my @lines = ($txt =~ /<a\s+href="([^"]*)"\s*>/g  );

my %hash   = map { $_, 1 }
	grep { $_ ne '' }
	map {
		# scheme
		s/^[a-z][a-z+\-.]+:\/\///;
		# user
		s/^[a-z0-9\-_.~%!$^'()*+,;=]+@//;
		# name
		s/^([a-z0-9\-._~%]+|[a-f0-9]+).*/$1/g;
		$_;
	} @lines;

@lines = sort map { "${_}\n" } (keys %hash);

print @lines;
