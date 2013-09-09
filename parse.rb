#
# parse.rb - Parse a sentence, outputting a syntax tree and logical form.
#

# Output directory and files.
OUTDIR = 'out'
SYNFILE = 'trees'
SEMFILE = 'lfs'


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

    # Null heads.
    tok = '' if tok == '[]'

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
      # Handle traces, light verbs, inflectional heads, and nulls.
      if @token == 'v' or @token == 't'
        s = "$#{s}$"
      elsif @parent.token == 'I'
        s = "[#{s}]"
      elsif @token == ''
        s = "$\\varnothing$"
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
prolog = ARGV.shift || 'dcg.pl'

# Get input from user.
print 'Sentence: '
words = gets.downcase.strip.split(/('s)\s+|(')\s+|\s+/)
sentence = words.map{|w| "'#{w.gsub("'", "\\\\'")}'"}.join(', ')

# Load and query.
loadf = "use_module(#{File.basename(prolog, '.pl')})"
query = "sentence([#{sentence}], S, I), write_ln(S), write_ln(I), fail."
swipl = ['swipl', '-g', loadf, '-t', query]


# Spawn a SWI-prolog.
trees, lfs = IO.popen(swipl, :err => [:child, :out]) do |io|
  lines = io.readlines

  # Pull out trees and interpretations.
  trees = lines.select { |s| s.start_with? ('cp(') }
  lfs   = lines.select { |s| s.start_with? ('[') }

  # Print query result.
  abort 'Sentence was rejected.' if trees.empty?
  puts trees, lfs

  trees.map! do |s|
    # Simplify DP's.
    s.gsub!(/dp\(d_\(d\(([\w\/. ]+)\)\)\)/, '*dp(\1)')
    s.gsub!(/dp\(d_\(np\(n_\(n\(([\w\/. ]+)\)\)\)\)\)/, '*dp(\1)')
    s.gsub!(/dp\(d_\(d\(([\w\/. ]+)\),\s*np\(n_\(n\(([\w\/. ]+)\)\)\)\)\)/, '*dp(\1 \2)')

    # Regexp for tokenizing the tree.
    re = /[\w*]+\(|\)|[\w\/.'\[\] ]+/

    # X-bar-ificate the tree output.
    s.scan(re).inject(XBarNode.new('')) do |node, token|
      if token == ')'
        node.parent
      else
        child = XBarNode.new(token)
        node.add_child child
        if child.node? then child else node end
      end
    end.children.first
  end

  lfs.map! do |s|
    # TeX-ify all the things!
    s.strip[1...-1].scan(/\w+\([^()]+\)/).map do |s|
      s.gsub(/\/(\d+)/, '_{\1}').gsub(/(\w+)([(),])/, '\text{\1}\2')
    end
  end

  [trees, lfs]
end


###############################################################################
#
#  Compile.
#

Dir.chdir(OUTDIR)

# LaTeX header/footer.
syn_preamble = %w{
  \documentclass[tikz,border=1cm]{standalone}
  \usepackage{amsmath, amssymb}
  \usepackage[T1]{fontenc}
  \usepackage[english]{babel}
  \usepackage{tikz-qtree}
  \begin{document}
} << ''

sem_preamble = %w{
  \documentclass[multi,border=1cm]{standalone}
  \usepackage{amsmath}
  \usepackage[T1]{fontenc}
  \usepackage[english]{babel}
  \standaloneenv{logform}
  \begin{document}
} << ''

epilogue = [''] + %w{
  \end{document}
}

# Format content.
trees.map! do |tree|
  [ '\begin{tikzpicture}', tree, '\end{tikzpicture}' ]
end
lfs.map! do |lf|
  [ '\begin{logform}', '$' + lf.join(' \land ') + '$', '\end{logform}' ]
end

# Write to LaTeX files.
File.open(SYNFILE + '.tex', 'w') do |f|
  f.puts(syn_preamble + trees + epilogue)
end
File.open(SEMFILE + '.tex', 'w') do |f|
  f.puts(sem_preamble + lfs + epilogue)
end

# Compile and open the PDFs.
`pdflatex #{SYNFILE + '.tex'}`
`pdflatex #{SEMFILE + '.tex'}`
`open #{SYNFILE + '.pdf'}`
`open #{SEMFILE + '.pdf'}`
