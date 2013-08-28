#
# test.rb - Run tests on a prolog DCG.
#

require 'rubygems'
require 'fiber'
require 'colorize'

prolog = ARGV.shift
abort 'Usage: test.rb grammar-file' if prolog.nil?

LOADF = "use_module(#{File.basename(prolog, '.pl')})"


###############################################################################
#
#  Testing DSL.
#

def sentence(s, &blk)
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

  puts "PASSED: ".green + s
end

def parse(syn, sem); Fiber.yield(syn, sem); end


###############################################################################
#
#  Tests.
#

sentence 'Max leaves.' do
  parse "cp(c_(ip(dp(d_(np(n_(n(max))))),i_(i(pres),vp(v_(v(leaves)))))))",
        "[pres(e/1),leave(e/1,max)]"
end

sentence 'Max left.' do
  parse "cp(c_(ip(dp(d_(np(n_(n(max))))),i_(i(pret),vp(v_(v(left)))))))",
        "[pret(e/1),leave(e/1,max)]"
end

sentence 'The boy leaves.' do
  parse "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pres),vp(v_(v(leaves)))))))",
        "[pres(e/1),leave(e/1,x/1),boy(x/1)]"
end
