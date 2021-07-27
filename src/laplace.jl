struct Laplace <: Function
    x
    s
    Laplace(x, s) = new(value(x), value(s))
end

# Indicate that no laplace is defined
struct NoLaplace end
laplace(f, x, s, v) = NoLaplace()

(L::Laplace)(x) = Term{symtype(x)}(L, [x])
(L::Laplace)(x::Num) = Num(L(value(x)))

is_laplace_transform(x::Term) = operation(x) isa Laplace
is_laplace_transform(x) = false

SymbolicUtils.promote_symtype(::Laplace, x) = x

Base.show(io::IO, L::Laplace) = print(io, "Laplace(", L.x, ", ", L.s, ")")

Base.:(==)(L1::Laplace, L2::Laplace) = isequal(L1.x, L2.x) && isequal(L1.s, L2.s)
Base.isequal(L1::Laplace, L2::Laplace) = isequal(L1.x, L2.x) && isequal(L1.s, L2.s)

function haslaplace(O)
    istree(O) ? operation(O) isa Laplace || any(haslaplace, arguments(O)) : false
end

laplace_idx(O::Any, ::Any) = 0
function laplace_idx(O::Symbolic, idx)
    istree(O) ? laplace(operation(O), (arguments(O)...,), Val(idx)) : 0
end

"""
$(SIGNATURES)

TODO
"""
function expand_laplace(O::Symbolic, simplify=false; occurances=nothing)
    if istree(O) && isa(operation(O), Laplace)
        @assert length(arguments(O)) == 1
        arg = expand_laplace(arguments(O)[1], false)

        if occurances === nothing
            occurances = occursin_info(operation(O).x, arg)
        end

        _isfalse(occurances) && return arg*inv(operation(O).s)
        if occurances isa Bool
         return inv(operation(O).s^2) # means it's a `true`
        end

        L = operation(O)

        if !istree(arg)
            return L(arg) # Cannot expand
        elseif isa(operation(arg), Sym)
            inner_args = arguments(arg)
            if any(isequal(L.x), inner_args)
                return L(arg) # base case if any argument is directly equal to the i.v.
            elseif islinear(arg, L.x)
                return sum(inner_args, init=0) do a # Chain rule?
                    return expand_laplace(L(a))
                end
            else
                return 
            end
        elseif isa(operation(arg), typeof(IfElse.ifelse)) # TODO: Fix this
            args = arguments(arg)
            op = operation(arg)
            O = op(args[1], D(args[2]), D(args[3]))
            return expand_derivatives(O, simplify; occurances)
        elseif isa(operation(arg), Laplace)
            # The recursive expand_derivatives was not able to remove
            # a nested Differential. We can attempt to differentiate the
            # inner expression wrt to the outer iv. And leave the
            # unexpandable Differential outside.
            if isequal(operation(arg).x, L.x)
                return L(arg)
            else
                inner = expand_laplace(L(arguments(arg)[1]), false)
                # if the inner expression is not expandable either, return
                if istree(inner) && operation(inner) isa Laplace
                    return L(arg)
                else
                    return expand_laplace(operation(arg)(inner), simplify)
                end
            end
#=         elseif isa(operation(arg), Integral) ## Why even try this one
            if isa(operation(arg).domain, AbstractInterval)
                domain = operation(arg).domain
                a, b = DomainSets.endpoints(domain)
                c = 0
                inner_function = expand_derivatives(arguments(arg)[1])
                if istree(value(a))
                    t1 = SymbolicUtils.substitute(inner_function, Dict(operation(arg).x => value(a)))
                    t2 = D(a)
                    c -= t1*t2
                end
                if istree(value(b))
                    t1 = SymbolicUtils.substitute(inner_function, Dict(operation(arg).x => value(b)))
                    t2 = D(b)
                    c += t1*t2
                end
                inner = expand_derivatives(D(arguments(arg)[1]))
                c += operation(arg)(inner)
                return value(c)
            end =#
        end
        ## Add a detection for differential!

        l = length(arguments(arg))
        exprs = []
        c = 0

        for i in 1:l
            t2 = expand_laplace(L(arguments(arg)[i]),false, occurances=arguments(occurances)[i])

            x = if _iszero(t2)
                t2
            elseif _isone(t2)
                d = laplace_idx(arg, i)
                d isa NoLaplace ? L(arg) : d
            else
                t1 = laplace_idx(arg, i)
                t1 = t1 isa NoLaplace ? D(arg) : t1
                t1 * t2
            end

            if _iszero(x)
                continue
            elseif x isa Symbolic
                push!(exprs, x)
            else
                c += x
            end
        end

        if isempty(exprs)
            return c
        elseif length(exprs) == 1
            term = (simplify ? SymbolicUtils.simplify(exprs[1]) : exprs[1])
            return _iszero(c) ? term : c + term
        else
            x = +((!_iszero(c) ? vcat(c, exprs) : exprs)...)
            return simplify ? SymbolicUtils.simplify(x) : x
        end
#=     elseif istree(O) && isa(operation(O), Integral)
        return operation(O)(expand_derivatives(arguments(O)[1])) =#
    elseif !haslaplace(O)
        return O
    else
        args = map(a->expand_derivatives(a, false), arguments(O))
        O1 = operation(O)(args...)
        return simplify ? SymbolicUtils.simplify(O1) : O1
    end
end

expand_laplace(x, simplify=false;occurances=nothing) = x

function expand_laplace(n::Num, simplify=false; occurances=nothing)
    Num(expand_laplace(value(n), simplify; occurances=occurances))
end

function laplace(O, x, s; simplify=false)
    if O isa AbstractArray
        Num[Num(expand_laplace(Laplace(x,s)(value(o)), simplify)) for o in O]
    else
        Num(expand_laplace(Laplace(x,s)(value(O)), simplify))
    end
end

laplace(::typeof(one), args::Tuple{<:Any}, ::Val{s}) where {s} = 1/s
laplace(::typeof(+), args::NTuple{N,Any}, ::Val) where {N} = 1
laplace(::typeof(*), args::NTuple{N,Any}, ::Val{s}) where {s,N} = 1