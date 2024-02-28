#!/bin/env ruby

require 'open3'
require 'etc'
require 'optparse'

$opts = {
	:filter => /.*/,
	:'disallow-undeclared-secondary' => false,
	:wd => File.expand_path(__dir__),
}

opt_parser = OptionParser.new { |o|
	o.on '--help', 'show this message' do
		puts o
		exit 0
	end
	o.on '--filter=FILTER', 'regexp for selecting files to run based on path', Regexp
	o.on '--test-dir=DIR', "directory which scan for tests, defaults to #{$opts[:wd]}", String
	o.on '--runner=FILE', 'script that will be called with a file', String do |r|
		$opts[:runner] = File.expand_path r
	end
	o.on '--disallow-undeclared-secondary', 'treat checking ERROR_UNEXPECTED_* against primary ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION an error' do
		$opts[:'disallow-undeclared-secondary'] = true
	end
}
opt_parser.parse!(into: $opts)

Dir.chdir $opts[:wd]

if $opts[:runner].nil?
	puts 'provide --runner'
	puts opt_parser
	exit 1
end

$errs = 0
$tests = 0

class ThreadPool
	def initialize
		@max = Etc::nprocessors
		@threads = []
	end

	def wait
		while @threads.size > 0
			filter
		end
	end

	def filter
		sleep 0.05
		@threads.filter! { |t| t.alive? }
	end

	def run
		while @threads.size >= @max
			filter
		end
		@threads << Thread.new {
			yield
		}
	end
end

$lk = Mutex.new

def run_get_err(path, expected_error)
	real_path = File.expand_path path
	stdout_str, stderr_str, status = Open3.capture3($opts[:runner], real_path)
	got_err = '<unknown>'
	if stderr_str =~ /\bERROR_([a-zA-Z0-9_]+)\b/
		got_err = /\bERROR_([a-zA-Z0-9_]+)\b/.match(stderr_str)[0]
	end
	put_outs = Proc.new {
		if status != 0
			puts "\tdetected error is #{got_err}"
		end
		if stdout_str != ""
			puts "\tstdout"
			puts stdout_str.strip.gsub(/^/, "\t\t")
		end
		if stderr_str != ""
			puts "\tstderr"
			puts stderr_str.strip.gsub(/^/, "\t\t")
		end
	}
	if expected_error.nil?
		if status != 0
			$errs += 1
			$lk.synchronize {
				puts "✗ #{path} expected to succeed"
				put_outs.()
			}
			return
		end
	else
		if status == 0
			$errs += 1
			$lk.synchronize {
				puts "✗ #{path} expected to fail with #{expected_error}"
				put_outs.()
			}
			return
		end
		if got_err != expected_error
			fline = File.open(real_path, &:readline)
			if got_err != "ERROR_TODO" and fline.start_with? "//"
				possible_errors = fline.scan /\bERROR_[a-zA-Z_]*/
				if possible_errors.include? got_err
					puts "✓ #{path} matched secondary error\n\t#{got_err}\n\t#{expected_error} <- primary"
					return
				end
			end
			if expected_error == 'ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION' and got_err =~ /ERROR_(UNEXPECTED|NOT)_/
				sign = '!'
				if $opts[:'disallow-undeclared-secondary']
					sign = '✗'
					$errs += 1
				end
				puts "#{sign} #{path} undeclared secondary error\n\t#{got_err} <- got\n\t#{expected_error} <- primary"
				return
			end
			$errs += 1
			$lk.synchronize {
				puts "✗ #{path} expected to fail with #{expected_error}, failed with #{got_err}"
				put_outs.()
			}
			return
		end
	end
	puts "✓ #{path}"
end

tp = ThreadPool.new

Dir::glob("./**/ok/**/*.st") { |f|
	next if not (f =~ $opts[:filter])
	$tests += 1
	tp.run {
		run_get_err f, nil
	}
}

Dir::glob("./**/bad/**/*.st") { |f|
	next if not (f =~ $opts[:filter])
	$tests += 1
	m = /\/bad\/(?<err>[^\/]+)\//.match(f)
	tp.run {
		run_get_err f, m['err']
	}
}

tp.wait

puts "Failed #{$errs}/#{$tests}"
if $errs != 0
	exit false
end
