#!/bin/env ruby

require 'open3'
require 'etc'

Dir.chdir __dir__

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

def run_get_err(path, expected_error)
    real_path = File.expand_path path
    stdout_str, stderr_str, status = Open3.capture3(
        'stack', '--silent', 'exec',
        '--cwd=..',
        'stella-exe', real_path
    )
    got_err = '<unknown>'
    if stderr_str =~ /\bERROR_([a-zA-Z0-9_]+)\b/
        got_err = /\bERROR_([a-zA-Z0-9_]+)\b/.match(stderr_str)[0]
    end
    put_outs = Proc.new {
        if status != 0
            puts "\tdetected error is #{got_err}"
        end
        if stdout_str != ""
            puts stdout_str.gsub(/^/, "\t")
        end
        if stderr_str != ""
            puts stderr_str.gsub(/^/, "\t")
        end
    }
    if expected_error.nil?
        if status != 0
            $errs += 1
            puts "✗ #{path} expected to succeed"
            put_outs.()
            return
        end
    else
        if status == 0
            $errs += 1
            puts "✗ #{path} expected to fail with #{expected_error}"
            put_outs.()
            return
        end
        if got_err != expected_error
            $errs += 1
            puts "✗ #{path} expected to fail with #{expected_error}, failed with #{got_err}"
            put_outs.()
            return
        end
    end
    puts "✓ #{path}"
end

tp = ThreadPool.new

Dir::glob("./golden/ok/**/*.st") { |f|
    $tests += 1
    tp.run {
        run_get_err f, nil
    }
}

Dir::glob("./golden/bad/**/*.st") { |f|
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
