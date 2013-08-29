#
# agreement.rb - Test for basic agreement.
#

accept 'Max lives.' do
  parse "cp(c_(ip(dp(d_(np(n_(n(max))))),i_(i(pres),vp(v_(v(lives)))))))",
        "[pres(e/1),live(e/1,max)]"
end

accept 'Max lived.' do
  parse "cp(c_(ip(dp(d_(np(n_(n(max))))),i_(i(pret),vp(v_(v(lived)))))))",
        "[pret(e/1),live(e/1,max)]"
end

accept 'The boy lives.' do
  parse "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pres),vp(v_(v(lives)))))))",
        "[pres(e/1),live(e/1,x/1),boy(x/1)]"
end

accept 'The boy lived.' do
  parse "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pret),vp(v_(v(lived)))))))",
        "[pret(e/1),live(e/1,x/1),boy(x/1)]"
end

accept 'The boys live.' do
  parse "cp(c_(ip(dp(d_(d(the),np(n_(n(boys))))),i_(i(pres),vp(v_(v(live)))))))",
        "[pres(e/1),live(e/1,x/1),boys(x/1)]"
end

accept 'The boys lived.' do
  parse "cp(c_(ip(dp(d_(d(the),np(n_(n(boys))))),i_(i(pret),vp(v_(v(lived)))))))",
        "[pret(e/1),live(e/1,x/1),boys(x/1)]"
end

reject 'Max live.'

reject 'The boy live.'

reject 'The boys lives.'

accept 'The boys meet the girl.' do
  parse "cp(c_(ip(dp(d_(d(the),np(n_(n(boys))))),i_(i(pres),vp(v_(v(meet),dp(d_(d(the),np(n_(n(girl)))))))))))",
        "[pres(e/1),meet(e/1,x/1,x/2),girl(x/2),boys(x/1)]"
end
