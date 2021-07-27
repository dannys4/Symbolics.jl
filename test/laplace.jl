using Symbolics
import Symbolics: Laplace, laplace, derivative
##
@variables x s
res_d = derivative(2x+1, x)
res = laplace(2x+1, x, s)
println(res)