#
# unit.rb - Run tests on a syntax/semantics engine.
#

require 'rubygems'
require 'fiber'
require 'colorize'

prolog = ARGV.shift || 'dcg.pl'

LOADF = "use_module(#{File.basename(prolog, '.pl')})"


###############################################################################
#
#  Basic testing DSL.
#

def sentence(s, success, &blk)
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

    if not syntax.delete syn
      puts "SYNTAX ERROR:".red, "  #{s}", "  #{syn}"
      return
    end

    if not semantics.delete sem
      puts "SEMANTICS ERROR:".red, "  #{s}", "  #{sem}"
      return
    end
  end

  if not syntax.empty?
    puts "EXTRANEOUS PARSES for ".red + s + ":".red
    syntax.each { |l| puts "  #{l}" }
    return
  end

  puts "#{success}: ".green + s
end

def parse(syn, sem); Fiber.yield(syn, sem); end

def accept(s, &blk); sentence s, "ACCEPTED", &blk; end
def reject(s); sentence s, "REJECTED" do; end; end

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
