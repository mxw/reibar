#
# unit.rb - Run tests on a syntax/semantics engine.
#

require 'rubygems'
require 'colorize'
require 'fiber'
require 'optparse'
require 'ostruct'

@options = OpenStruct.new

OptionParser.new do |opts|
  opts.banner = "Usage: ruby unit.rb [options] [grammar-file]"

  opts.on("-v", "--verbose", "Run verbosely") do |o|
    @options.verbose = o
  end

  opts.on("-a", "--all", "Run all tests") do |o|
    @options.all = o
  end
end.parse!

prolog = ARGV.shift || 'dcg.pl'

LOADF = "use_module(#{File.basename(prolog, '.pl')})"


###############################################################################
#
#  Basic testing DSL.
#

def sentence(s, success, opts, &blk)
  fiber = Fiber.new &blk

  words = s.downcase.strip.gsub('.', '').split(/('s)\s+|(')\s+|\s+/)
  sentence = words.map{|w| "'#{w.gsub("'", "\\\\'")}'"}.join(', ')

  query = "sentence([#{sentence}], S, I), write_ln(S), write_ln(I), fail."
  swipl = ['swipl', '-g', LOADF, '-t', query]

  syntax, semantics = IO.popen(swipl, :err => [:child, :out]) do |io|
    lines = io.readlines.map { |l| l.strip }

    [ lines.select { |s| s.start_with? ('cp(') },
      lines.select { |s| s.start_with? ('[') },
    ]
  end

  while fiber.alive? && (out = fiber.resume) do
    syn, sem = out

    begin
      syntax.delete_at(syntax.index(syn))
    rescue TypeError
      puts "SYNTAX ERROR:".red, "  #{s}", "  #{syn}"
      return
    end

    begin
      semantics.delete_at(semantics.index(sem))
    rescue TypeError
      puts "SEMANTICS ERROR:".red, "  #{s}", "  #{sem}"
      return
    end
  end

  if not syntax.empty?
    puts "EXTRANEOUS PARSES for ".red + s + ":".red
    syntax.each { |l| puts "  #{l}" }
    return
  end

  puts "#{success}: ".green + s unless opts[:quiet]
end

def as(pair); Fiber.yield(*pair.split(/\s*\n\s*/)); end

def accept(s, &blk);      sentence s, "ACCEPTED", {}, &blk; end
def reject(s, opts = {}); sentence s, "REJECTED", opts do; end; end

def test(s)
  puts "+--[#{s}]".upcase.blue
  load "./tests/#{s}.rb"
  puts ''
end


###############################################################################
#
#  Tests.
#

test 'fragment'
test 'agreement'
test 'theta'
test 'mode-aspect'
