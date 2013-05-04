#
# tree.rb - Generate a parse tree for a sentence.
#
# Based very loosely on an anonymous Piazza post for CS 187, 2013.
#

require 'set'

# Identifying prefix for syntax tree root.
PREFIX = 'cp'

# Output directory and files.
OUTDIR = 'out'
TEXFILE = 'trees.tex'
PDFFILE = 'trees.pdf'

#
# qtree_convert - Convert a SWI-prolog atom or metachar into a Qtree token.
#
# Node labels are tokenized with their open-paren.  Inflectional heads are
# tokenized with their full contents.
#
def qtree_convert(token, labels)
  token.gsub!('_', "$'$")

  # Lexical categories.
  if token.end_with? '('
    ' [.' + token.chop.capitalize.gsub('p', 'P')
  elsif token.start_with? 'i('
    ' [.I {[' + token[2...-1] + ']} ]'
  elsif token == ')'
    ' ]'
  elsif token == 's'
    ' {\'s}'

  # Head movement (i.e., labeled).
  elsif token.include? '/'
    # Token with a label means head movement.
    tok, label = token.split('/')

    # Determine which end of the arrow this node is at.
    if label.to_i.zero?
      tok, label = label, tok
      type = 'dst'
    else
      type = 'src'
    end

    # Italicize traces and light verbs.
    tok = "$#{tok}$" if tok.size == 1

    # Give the node an alphabetic label.
    labels[label] ||= labels[:label].succ!.dup

    # Output a qtree node.
    " \\node(#{labels[label]} #{type}){#{tok}};"
  else
    ' {' + token + '}'
  end
end

# Shift the Prolog file.
prolog = ARGV.shift
abort 'Usage: tree.rb grammar-file' if prolog.nil?

# Get input from user.
print 'Sentence: '
sentence = gets.downcase.gsub(/[.']/, ' ').strip.split.join(', ')

# Load and query.
loadf = "use_module(#{File.basename(prolog, '.pl')})"
query = "sentence([#{sentence}], S, _), write_ln(S), fail."
swipl = ['swipl', '-g', loadf, '-t', query]

# Spawn a SWI-prolog.
trees = IO.popen(swipl, :err => [:child, :out]) do |io|
  # Pull out valid syntax trees.
  trees = io.readlines.select { |s| s.start_with? (PREFIX + '(') }

  # Print query result.
  abort 'Sentence was rejected.' if trees.empty?
  puts trees

  trees.map do |s|
    # Regexp for tokenizing the tree.
    re = /i\(\w+\)|\w+\(|\)|[\w\/. ]+/

    # Hash of head movement source/dest labels.
    labels = {label: '`'}

    # Q-tree-ificate the tree outputs.
    qtree = s.scan(re).inject('\Tree') do |qtree, token|
      qtree << qtree_convert(token, labels)
    end

    labels.delete :label
    labels.each do |_, l|
      qtree << "\n\\draw[semithick,->] "
      qtree << "(#{l} src)..controls +(south:6) and +(south:11)..(#{l} dst);"
    end

    qtree
  end
end

# LaTeX header/footer.
PREAMBLE = %w{
	\documentclass{article}
  \usepackage{geometry}
  \usepackage[T1]{fontenc}
  \usepackage[english]{babel}
  \usepackage{tikz}
  \usepackage{tikz-qtree}
  \pagestyle{empty}
  \begin{document}
} << ''

EPILOGUE = [''] + %w{
  \end{document}
}

# Wrap trees.
trees.map! do |qtree|
  [ '\begin{center}',
    '\begin{tikzpicture}',
    qtree,
    '\end{tikzpicture}',
    '\end{center}',
  ]
end

# Change to out directory.
Dir.chdir(OUTDIR)

# Write to LaTeX file.
File.open(TEXFILE, 'w') do |f|
  f.puts(PREAMBLE + trees + EPILOGUE)
end

# Compile and open the PDF.
`pdflatex #{TEXFILE}`
`open #{PDFFILE}`
