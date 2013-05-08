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


###############################################################################
#
#  X-bar theory syntax tree node.
#

class XBarNode
  attr_accessor :parent
  attr_reader :type, :children, :token

  def initialize(tok)
    @type = :leaf
    @parent = nil
    @children = []
    @label = nil
    @movtype = nil

    # Lexical categories are nodes; words are leaves.
    if tok.end_with? '('
      @type = :node

      # Whether or not to use a roof.
      if tok.start_with? '*'
        tok = tok[1..-1]
        @roof = true
      end

      tok = tok.chop.capitalize.gsub('p', 'P')
    end

    # Head movement source and destination.
    if tok.include? '/'
      tok, label = tok.split('/')

      if label.to_i.zero?
        tok, label = label, tok
        @movtype = :dst
      else
        @movtype = :src
      end

      @label = label
    end

    # Set the final token.
    @token = tok
  end

  def node?; @type == :node; end
  def leaf?; @type == :leaf; end

  def add_child(child)
    @children << child
    child.parent = self
  end

  #
  # Output the subtree in Qtree format.
  #
  def to_s
    s, ddata = stringify(0, '`', {})

    s = '\Tree' + s

    # Draw head movement arrows.
    ddata.each_value.inject(s) do |s, d|
      # Compute arrow offset based on depths.
      sdep = (2 * (4 + d[:depth] - d[:src])).to_i
      ddep = (1.5 * (2 + d[:depth] - d[:dst])).to_i

      l = d[:label]
      sctl = "+(south:#{sdep})"
      dctl = "+(south:#{ddep})"

      s << "\n\\draw[semithick,->] "
      s << "(#{l} src)..controls #{sctl} and #{dctl}..(#{l} dst);"
    end
  end

  #
  # Stringify the subtree as a Qtree, but also return depth-related metadata
  # for optimizing head movement.
  #
  def stringify(depth, lstr, ddata)
    # Replace underscores with '.
    s = @token.gsub('_', "$'$")

    # Stringify leaves.
    if @type == :leaf
      # Italicize traces, light verbs, and inflectional heads.
      if @token == 'v' or @token == 't'
        s = "$#{s}$"
      elsif @parent.token == 'I'
        s = "[#{s}]"
      end

      if not @label.nil?
        # Head movement label accounting.
        if not ddata.key? @label
          ddata[@label] = { label: lstr.succ!.dup, depth: depth, }
        end
        ddata[@label][@movtype] = depth
        ddata[@label][:depth] = [ddata[@label][:depth], depth].max

        # Output a TikZ node.
        s = " \\node(#{ddata[@label][:label]} #{@movtype}){#{s}};"
      else
        s = " {#{s}}"
      end

    # Stringify nodes.
    elsif @type == :node
      # Append roof string.
      s += ' \edge[roof];' if @roof

      # Stringify children.
      cs = @children.map { |c| c.stringify(depth + 1, lstr, ddata).first }

      s = " [.#{s} #{cs.join(' ')} ]"
    end

    # Update high water mark depth for unmatched labels.
    ddata.each_value do |d|
      d[:depth] = [d[:depth], depth].max unless d.key? :src and d.key? :dst
    end

    # Return string and depth data.
    return s, ddata
  end
end


###############################################################################
#
#  Parse.
#

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
    # Simplify DP's.
    s.gsub!(/dp\(d_\(np\(n_\(n\(([\w\/. ]+)\)\)\)\)\)/, '*dp(\1)')
    s.gsub!(/dp\(d_\(d\(([\w\/. ]+)\),\s*np\(n_\(n\(([\w\/. ]+)\)\)\)\)\)/, '*dp(\1 \2)')

    # Regexp for tokenizing the tree.
    re = /[\w*]+\(|\)|[\w\/. ]+/

    # X-bar-ificate the tree output.
    tree = s.scan(re).inject(XBarNode.new('')) do |node, token|
      if token == ')'
        node.parent
      else
        child = XBarNode.new(token)
        node.add_child child
        if child.node? then child else node end
      end
    end.children.first

    tree
  end
end


###############################################################################
#
#  Compile.
#

# LaTeX header/footer.
PREAMBLE = %w{
  \documentclass[tikz,border=1cm]{standalone}
  \usepackage[T1]{fontenc}
  \usepackage[english]{babel}
  \usepackage{tikz-qtree}
  \begin{document}
} << ''

EPILOGUE = [''] + %w{
  \end{document}
}

# Wrap trees.
trees.map! do |tree|
  [ '\begin{tikzpicture}',
    tree,
    '\end{tikzpicture}',
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
