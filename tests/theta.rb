#
# theta.rb - Test theta roles.
#

reject 'Max lives Max.'

reject 'The boys live the girl.'

reject 'The boy meets.'

reject 'The boy meets the girl a cake.'

accept 'The boy meets the girl.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pres),vp(v_(v(meets),dp(d_(d(the),np(n_(n(girl)))))))))))
  [pres(e/1),meet(e/1,x/1,x/2),girl(x/2),boy(x/1)]"
end

accept 'The boy bakes.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pres),vp(v_(v(bakes)))))))
  [pres(e/1),bake(e/1,x/1),boy(x/1)]"
end

accept 'The boy bakes a cake.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pres),vp(v_(v(bakes),dp(d_(d(a),np(n_(n(cake)))))))))))
  [pres(e/1),bake(e/1,x/1,x/2),cake(x/2),boy(x/1)]"
end

accept 'The boy bakes the girl a cake.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pres),vp(v_(v(1/v),vp(dp(d_(d(the),np(n_(n(girl))))),v_(v(bakes/1),dp(d_(d(a),np(n_(n(cake)))))))))))))
  [pres(e/1),bake(e/1,x/1,x/3),to(e/1,x/2),girl(x/2),cake(x/3),boy(x/1)]"
end

reject 'The boy gives'

reject 'The boy gives the girl.'

accept 'The boy gives the girl a cake.' do
  as "cp(c_(ip(dp(d_(d(the),np(n_(n(boy))))),i_(i(pres),vp(v_(v(1/v),vp(dp(d_(d(the),np(n_(n(girl))))),v_(v(gives/1),dp(d_(d(a),np(n_(n(cake)))))))))))))
  [pres(e/1),give(e/1,x/1,x/3),to(e/1,x/2),girl(x/2),cake(x/3),boy(x/1)]"
end
