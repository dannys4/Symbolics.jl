using Symbolics
import Symbolics: Laplace, laplace, derivative
_ts = Any[]
_os = Any[]
@variables x s
res_d = derivative(x, x)
res = laplace(2x+1, x, s)
println(res)