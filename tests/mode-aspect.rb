#
# mode-aspect.rb - Test mode and aspect.
#

accept 'The boy goes.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pres),vp(v_(v(goes)))))))
  [pres(e/1),go(e/1,x/1),boy(x/1)]"
end

@infl = OpenStruct.new
@infl.boy = %w{boy boys}
@infl.go = %w{go goes went going gone}
@infl.do = %w{do does did doing done}
@infl.can = %w{can could}
@infl.have = %w{have has had having had}
@infl.be = %w{be am is are was were being been}

def combine(*args)
  args.shift.product(*args).map { |a| a.join(' ') + '.' }
end

def quiet_wrap
  print '(Quietly testing rejects... '.yellow unless @options.verbose
  yield
  puts 'done)'.yellow unless @options.verbose
end

##########################################

puts "\n...DO SUPPORT".cyan

quiet_wrap do
  combine(['The'], @infl.boy, @infl.do, @infl.go).each do |s|
    next if [
      'The boy does go.',
      'The boy did go.',
      'The boys do go.',
      'The boys did go.',
    ].include? s

    reject s, quiet: !@options.verbose
  end
end

accept 'The boy does go.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(does),vp(v_(v(go)))))))
  [pres(e/1),go(e/1,x/1),boy(x/1)]"
end

accept 'The boy did go.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(did),vp(v_(v(go)))))))
  [pret(e/1),go(e/1,x/1),boy(x/1)]"
end

accept 'The boys do go.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boys))))),i_(i(do),vp(v_(v(go)))))))
  [pres(e/1),go(e/1,x/1),boys(x/1)]"
end

accept 'The boys did go.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boys))))),i_(i(did),vp(v_(v(go)))))))
  [pret(e/1),go(e/1,x/1),boys(x/1)]"
end

##########################################

puts "\n...MODALITY".cyan

quiet_wrap do
  combine(['The'], @infl.boy, @infl.can, @infl.go).each do |s|
    next if [
      'The boy can go.',
      'The boy could go.',
      'The boys can go.',
      'The boys could go.',
    ].include? s

    reject s, quiet: !@options.verbose
  end
end

accept 'The boy can go.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pres),mp(m_(m(can),vp(v_(v(go)))))))))
  [pres(e/1),go(e/2,x/1),can(e/1,e/2),boy(x/1)]"
end

accept 'The boy could go.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pret),mp(m_(m(could),vp(v_(v(go)))))))))
  [pret(e/1),go(e/2,x/1),can(e/1,e/2),boy(x/1)]"
end

accept 'The boys can go.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boys))))),i_(i(pres),mp(m_(m(can),vp(v_(v(go)))))))))
  [pres(e/1),go(e/2,x/1),can(e/1,e/2),boys(x/1)]"
end

accept 'The boys could go.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boys))))),i_(i(pret),mp(m_(m(could),vp(v_(v(go)))))))))
  [pret(e/1),go(e/2,x/1),can(e/1,e/2),boys(x/1)]"
end

##########################################

puts "\n...PERFECTIVE".cyan

quiet_wrap do
  combine(['The'], @infl.boy, @infl.have, @infl.go).each do |s|
    next if [
      'The boy has gone.',
      'The boy had gone.',
      'The boys have gone.',
      'The boys had gone.',
    ].include? s

    reject s, quiet: !@options.verbose
  end
end

accept 'The boy has gone.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pres),perfp(perf_(perf(has),vp(v_(v(gone)))))))))
  [pres(e/1),go(e/2,x/1),have(e/1,e/2),boy(x/1)]"
end

accept 'The boy had gone.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pret),perfp(perf_(perf(had),vp(v_(v(gone)))))))))
  [pret(e/1),go(e/2,x/1),have(e/1,e/2),boy(x/1)]"
end

accept 'The boys have gone.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boys))))),i_(i(pres),perfp(perf_(perf(have),vp(v_(v(gone)))))))))
  [pres(e/1),go(e/2,x/1),have(e/1,e/2),boys(x/1)]"
end

accept 'The boys had gone.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boys))))),i_(i(pret),perfp(perf_(perf(had),vp(v_(v(gone)))))))))
  [pret(e/1),go(e/2,x/1),have(e/1,e/2),boys(x/1)]"
end

##########################################

puts "\n...PROGRESSIVE".cyan

quiet_wrap do
  combine(['The'], @infl.boy, @infl.be, @infl.go).each do |s|
    next if [
      'The boy is going.',
      'The boy was going.',
      'The boys are going.',
      'The boys were going.',
    ].include? s

    reject s, quiet: !@options.verbose
  end
end

accept 'The boy is going.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pres),progp(prog_(prog(is),vp(v_(v(going)))))))))
  [pres(e/1),go(e/2,x/1),be(e/1,e/2),boy(x/1)]"
end

accept 'The boy was going.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pret),progp(prog_(prog(was),vp(v_(v(going)))))))))
  [pret(e/1),go(e/2,x/1),be(e/1,e/2),boy(x/1)]"
end

accept 'The boys are going.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boys))))),i_(i(pres),progp(prog_(prog(are),vp(v_(v(going)))))))))
  [pres(e/1),go(e/2,x/1),be(e/1,e/2),boys(x/1)]"
end

accept 'The boys were going.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boys))))),i_(i(pret),progp(prog_(prog(were),vp(v_(v(going)))))))))
  [pret(e/1),go(e/2,x/1),be(e/1,e/2),boys(x/1)]"
end

##########################################

if @options.all
  puts "\n...MISORDERED".cyan

  def reject_aux_orders(n, opts = {})
    opts[:except] ||= []
    opts[:except].map!(&:sort)

    %w{do can have be}.map(&:to_sym).combination(n).each do |auxi|
      next if opts[:except].include? auxi.sort

      auxi = auxi.map { |aux| @infl.send aux }

      combine(['The'], @infl.boy, *auxi, @infl.go).each do |s|
        reject s, quiet: !@options.verbose
      end
    end
  end

  quiet_wrap do
    reject_aux_orders(2, except: [
      [:can, :have],
      [:can, :be],
      [:have, :be],
    ])

    reject_aux_orders(3, except: [
      [:can, :have, :be],
    ])

    reject_aux_orders(4)
  end
end

##########################################

puts "\n...MOD PERF".cyan

quiet_wrap do
  combine(['The'], @infl.boy, @infl.can, @infl.have, @infl.go).each do |s|
    next if [
      'The boy can have gone.',
      'The boy could have gone.',
      'The boys can have gone.',
      'The boys could have gone.',
    ].include? s

    reject s, quiet: !@options.verbose
  end
end

accept 'The boy can have gone.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pres),mp(m_(m(can),perfp(perf_(perf(have),vp(v_(v(gone)))))))))))
  [pres(e/1),go(e/3,x/1),can(e/1,e/2),have(e/2,e/3),boy(x/1)]"
end

accept 'The boy could have gone.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pret),mp(m_(m(could),perfp(perf_(perf(have),vp(v_(v(gone)))))))))))
  [pret(e/1),go(e/3,x/1),can(e/1,e/2),have(e/2,e/3),boy(x/1)]"
end

accept 'The boys can have gone.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boys))))),i_(i(pres),mp(m_(m(can),perfp(perf_(perf(have),vp(v_(v(gone)))))))))))
  [pres(e/1),go(e/3,x/1),can(e/1,e/2),have(e/2,e/3),boys(x/1)]"
end

accept 'The boys could have gone.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boys))))),i_(i(pret),mp(m_(m(could),perfp(perf_(perf(have),vp(v_(v(gone)))))))))))
  [pret(e/1),go(e/3,x/1),can(e/1,e/2),have(e/2,e/3),boys(x/1)]"
end

##########################################

puts "\n...PERF PROG".cyan

quiet_wrap do
  combine(['The'], @infl.boy, @infl.have, @infl.be, @infl.go).each do |s|
    next if [
      'The boy has been going.',
      'The boy had been going.',
      'The boys have been going.',
      'The boys had been going.',
    ].include? s

    reject s, quiet: !@options.verbose
  end
end

accept 'The boy has been going.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pres),perfp(perf_(perf(has),progp(prog_(prog(been),vp(v_(v(going)))))))))))
  [pres(e/1),go(e/3,x/1),have(e/1,e/2),be(e/2,e/3),boy(x/1)]"
end

accept 'The boy had been going.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pret),perfp(perf_(perf(had),progp(prog_(prog(been),vp(v_(v(going)))))))))))
  [pret(e/1),go(e/3,x/1),have(e/1,e/2),be(e/2,e/3),boy(x/1)]"
end

accept 'The boys have been going.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boys))))),i_(i(pres),perfp(perf_(perf(have),progp(prog_(prog(been),vp(v_(v(going)))))))))))
  [pres(e/1),go(e/3,x/1),have(e/1,e/2),be(e/2,e/3),boys(x/1)]"
end

accept 'The boys had been going.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boys))))),i_(i(pret),perfp(perf_(perf(had),progp(prog_(prog(been),vp(v_(v(going)))))))))))
  [pret(e/1),go(e/3,x/1),have(e/1,e/2),be(e/2,e/3),boys(x/1)]"
end

##########################################

puts "\n...MOD PROG".cyan

quiet_wrap do
  combine(['The'], @infl.boy, @infl.can, @infl.be, @infl.go).each do |s|
    next if [
      'The boy can be going.',
      'The boy could be going.',
      'The boys can be going.',
      'The boys could be going.',
    ].include? s

    reject s, quiet: !@options.verbose
  end
end

accept 'The boy can be going.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pres),mp(m_(m(can),progp(prog_(prog(be),vp(v_(v(going)))))))))))
  [pres(e/1),go(e/3,x/1),can(e/1,e/2),be(e/2,e/3),boy(x/1)]"
end

accept 'The boy could be going.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pret),mp(m_(m(could),progp(prog_(prog(be),vp(v_(v(going)))))))))))
  [pret(e/1),go(e/3,x/1),can(e/1,e/2),be(e/2,e/3),boy(x/1)]"
end

accept 'The boys can be going.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boys))))),i_(i(pres),mp(m_(m(can),progp(prog_(prog(be),vp(v_(v(going)))))))))))
  [pres(e/1),go(e/3,x/1),can(e/1,e/2),be(e/2,e/3),boys(x/1)]"
end

accept 'The boys could be going.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boys))))),i_(i(pret),mp(m_(m(could),progp(prog_(prog(be),vp(v_(v(going)))))))))))
  [pret(e/1),go(e/3,x/1),can(e/1,e/2),be(e/2,e/3),boys(x/1)]"
end

##########################################

puts "\n...MOD PERF PROG".cyan

quiet_wrap do
  combine(['The'], @infl.boy, @infl.can, @infl.have, @infl.be,
          @infl.go).each do |s|
    next if [
      'The boy can have been going.',
      'The boy could have been going.',
      'The boys can have been going.',
      'The boys could have been going.',
    ].include? s

    reject s, quiet: !@options.verbose
  end
end

accept 'The boy can have been going.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pres),mp(m_(m(can),perfp(perf_(perf(have),progp(prog_(prog(been),vp(v_(v(going)))))))))))))
  [pres(e/1),go(e/4,x/1),can(e/1,e/2),have(e/2,e/3),be(e/3,e/4),boy(x/1)]"
end

accept 'The boy could have been going.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pret),mp(m_(m(could),perfp(perf_(perf(have),progp(prog_(prog(been),vp(v_(v(going)))))))))))))
  [pret(e/1),go(e/4,x/1),can(e/1,e/2),have(e/2,e/3),be(e/3,e/4),boy(x/1)]"
end

accept 'The boys can have been going.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boys))))),i_(i(pres),mp(m_(m(can),perfp(perf_(perf(have),progp(prog_(prog(been),vp(v_(v(going)))))))))))))
  [pres(e/1),go(e/4,x/1),can(e/1,e/2),have(e/2,e/3),be(e/3,e/4),boys(x/1)]"
end

accept 'The boys could have been going.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boys))))),i_(i(pret),mp(m_(m(could),perfp(perf_(perf(have),progp(prog_(prog(been),vp(v_(v(going)))))))))))))
  [pret(e/1),go(e/4,x/1),can(e/1,e/2),have(e/2,e/3),be(e/3,e/4),boys(x/1)]"
end
