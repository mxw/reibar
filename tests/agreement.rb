#
# agreement.rb - Test for basic agreement.
#

accept 'Max goes.' do
  parse "cp(c_(ip(dp(d_(np(n_(n(max))))),i_(i(pres),vp(v_(v(goes)))))))",
        "[pres(e/1),go(e/1,max)]"
end

accept 'Max went.' do
  parse "cp(c_(ip(dp(d_(np(n_(n(max))))),i_(i(pret),vp(v_(v(went)))))))",
        "[pret(e/1),go(e/1,max)]"
end

accept 'The boy goes.' do
  parse "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pres),vp(v_(v(goes)))))))",
        "[pres(e/1),go(e/1,x/1),boy(x/1)]"
end

accept 'The boy went.' do
  parse "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pret),vp(v_(v(went)))))))",
        "[pret(e/1),go(e/1,x/1),boy(x/1)]"
end

accept 'The boys go.' do
  parse "cp(c_(ip(dp(d_(d(the),np(n_(n(boys))))),i_(i(pres),vp(v_(v(go)))))))",
        "[pres(e/1),go(e/1,x/1),boys(x/1)]"
end

accept 'The boys went.' do
  parse "cp(c_(ip(dp(d_(d(the),np(n_(n(boys))))),i_(i(pret),vp(v_(v(went)))))))",
        "[pret(e/1),go(e/1,x/1),boys(x/1)]"
end

reject 'Max live.'

reject 'The boy go.'

reject 'The boy going.'

reject 'The boy gone.'

reject 'The boys goes.'

accept 'The boys meet the girl.' do
  parse "cp(c_(ip(dp(d_(d(the),np(n_(n(boys))))),i_(i(pres),vp(v_(v(meet),dp(d_(d(the),np(n_(n(girl)))))))))))",
        "[pres(e/1),meet(e/1,x/1,x/2),girl(x/2),boys(x/1)]"
end
