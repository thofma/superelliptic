#  Copyright (C) 2009-2011 Moriz Minzlaff <minzlaff@daad-alumni.de>
#
#  This program is free software: you can redistribute it and/or modify
#  it under the terms of the GNU General Public License as published by
#  the Free Software Foundation, either version 3 of the License, or
#  (at your option) any later version.
#
#  This program is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with this program.  If not, see <http://www.gnu.org/licenses/>.
#

#*****************************************************************************
#
# This package implements Minzlaff's algorithm for computing zeta functions of
# superelliptic curves in larger characteristic [1].
#
# [1] Minzlaff, M.: Computing Zeta Functions of Superelliptic Curves in Larger
#   Characteristic. Mathematics in Computer Science. 3(2), 209--224 (2010)
#
#*****************************************************************************

include("linearrecurrence.jl")
import AbstractAlgebra.Ring
import AbstractAlgebra.Generic

# Some dumb useless to everyone else functions that let me use nmod as if it were padic
function Nemo.frobenius(a::Union{Nemo.nmod, Generic.Res{fmpz}})
    return a
end

function Nemo.degree(R::Nemo.GaloisField)
    return 1
end

function Nemo.degree(R::ResRing{fmpz})
    return 1
end

function Nemo.degree(R::Nemo.NmodRing)
    return 1
end

# A few generalities on the differentials and the spaces W_{s,t}:
# The differential x^iy^j dx lies in
#    the iota-th block of W_{s,t}
# with
#    s \in \{ i, i-1, ..., max{-1, i- (b-1)} \}
#    t = (j div a)+1 if j \ge 0
#    t = (-j div a) if j < 0
#    iota = a - (j rem a) if j \ge 0
#    iota = (-j rem a) if j < 0

function Row(j,a)
#    Returns row index of x^...y^j dx
#
#    INPUT:
#
#    - ``j`` - a finite cardinal
#    - ``a`` - a finite cardinal

    if (j >= 0)
        return div(j, a)+1
    else
        return div((-j), a)
    end
end

function Block(j,a)
#    Returns block index of x^...y^j dx
#
#    INPUT:
#
#    - ``j`` - a finite cardinal
#    - ``a`` - a finite cardinal

    if (j >= 0)
        return a -  mod(j, a)
    else
        return mod(-j, a)
    end
end

function ScalarCoefficients(j, k, a, hk, p, q, N)
# Returns the scalar coefficients \mu_{k,r,j}, i.e.
#    res_[r] = \mu_{k,r-1,j}
# (note the shift by 1 in the argument r!)
# the sequence has length b*k+1

    R1 = base_ring(hk)
    res_ = [zero(R1) for r in 1:degree(hk)+1]

    for r = 0:degree(hk)
        lambda = coeff(hk, r)
        # num = numerator of the two binomial expressions
        num = 1
        for i = 0:N-2
            num = num*(-(j//a)-i)
        end
        # denom = denominator of the two binomial expressions
        denom = factorial(k)*factorial((N-1)-k)
        # last summand
        summand = num//denom
        sum = (-1)^(N-1+k)*summand
        # summing up going down
        for l = (N-2):-1:k
            summand = summand*(l+1-k)//(-(j//a)-l)
            sum = sum + (-1)^(l+k)*summand
        end
        sum = R1(numerator(sum))*inv(R1(denominator(sum)))
        res_[r+1] = p*lambda*sum
    end

    return res_
end

function RSCombination(h)
# returns polynomial sequences r_ and s_ such that
# r_[i]h + s_[i]Derivative(h) = x^i
# where i \le b-2 and deg r_[i] \le b-2. deg s_[i] \le b-1

    b = degree(h)
    rk = b+(b-1)
    R = base_ring(parent(h))
    RMat = MatrixSpace(R, rk, rk)

    dh = derivative(h)

    M = zero(RMat)
    for c = 1:rk
        for r = 1:b-1
            if ((c-1)-(r-1) >= 0)
                M[r,c] = coeff(h, (c-1)-(r-1))
            end
        end
        for r = b:rk
            if ((c-1)-(r-b) >= 0)
                M[r,c] = coeff(dh, (c-1)-(r-b))
            end
        end
    end
    Mi = inv(M)
    if Mi isa Tuple
        Mi = divexact(Mi[1],Mi[2])
    end

    resR_ = [ parent(h)([ Mi[i,c] for c in 1:(b-1) ]) for i in 1:(b-1) ]
    resS_ = [ parent(h)([ Mi[i,c] for c in b:rk ]) for i in 1:(b-1) ]

    return resR_, resS_
end

function CastElement(R, e)
#    Return the image / a preimage of e in R
#
#    INPUT:
#
#    -  ``R`` - (a polynomial ring over) UnramifiedQuotientRing(K,N)
#    -  ``e`` - an element of (or a polynomial over)
#               UnramifiedQuotientRing(K,N') with N' = N-1 or N+1
#
#    OUTPUT:
#
#    An element of R
#
#    NOTE:
#
#    This function is needed since Magma cannot coerce between
#    UnramifiedQuotientRing(K,N) with different N

    RR = base_ring(R)
    # If K/L with L prime, then RR is the UnramifiedQuotientRing(L,N)
    # If R is not a polynomial ring, then (RR eq RRR)
    RRR = base_ring(RR)
    e_ = Eltseq(e)
    res_ = []
    for i = 1:length(e_)
        e__ = Eltseq(e_[i])
        res__ = []
        for j = 1:length(e__)
            res__[j] = RRR(e__[j])
        end
        res_[i] = RR(res__)
    end
    return R(res_)
end


function CastMatrix(R, M)
#    Return the image / a preimage of M over R
#
#    INPUT:
#
#    -  ``R`` - a (polynomial) matrix ring over UnramifiedQuotientRing(K,N)
#    -  ``M`` - a (polynomial) matrix over UnramifiedQuotientRing(K,N') with
#               N' = N-1 or N+1
#
#    OUTPUT:
#
#    An element of R
#
#    NOTE:
#
#    This function is needed since Magma cannot coerce between
#    UnramifiedQuotientRing(K,N) with different N
#
    RR = base_ring(R)
    res = zero_matrix(RR, rows(M), cols(M))
    for i = 1:rows(M)
        for j = 1:cols(M)
            res[i,j] = cast_poly_nmod(RR, M[i,j])
        end
    end
    return res
end

function CastBaseMatrix(R, M)
#    Return the image / a preimage of M over R
#
#    INPUT:
#
#    -  ``R`` - a (polynomial) matrix ring over UnramifiedQuotientRing(K,N)
#    -  ``M`` - a (polynomial) matrix over UnramifiedQuotientRing(K,N') with
#               N' = N-1 or N+1
#
#    OUTPUT:
#
#    An element of R
#
#    NOTE:
#
#    This function is needed since Magma cannot coerce between
#    UnramifiedQuotientRing(K,N) with different N
#
    RR = base_ring(R)
    res = zero_matrix(RR, rows(M), cols(M))
    for i = 1:rows(M)
        for j = 1:cols(M)
            res[i,j] = RR(lift_elem(M[i,j]))
        end
    end
    return res
end

function HRedMatrix(t, iota, a, h, R1PolMatH, pts = [])
# given row index t and block index iota,
# the equation of the curve (via a,h)
# return the horizontal reduction matrix
# for row t and block iota
# also return the denominators as a sequence of polynomials
# i.e.
# resM = M_H^{t,\iota}(s)
# resD = d_H^{t,\iota}(s)
#
    println(t, iota, a, h, R1PolMatH)
    R1Pol = parent(h)
    s = gen(R1Pol)

    resM = zero(R1PolMatH)

    b = degree(h)
    lambda = lead(h)
    h1 = h - lambda*s^b # h - leading term (h)

    resD =  lambda*(b*(a*t+iota-a) -a*s)
    c_ = [ a*coeff(h1, 0)*s ]
    c_ = vcat(c_, [ R1Pol(a*coeff(h1, i)*s -
                          (a*t+iota-a)*coeff(derivative(h1), i-1)) for i in 1:(b-1) ])

    for i = 1:b-1
        resM[i,i+1] = resD
    end
    for i = 1:b
        resM[b,i] = c_[i]
    end

    return resM, resD
end

function HRedMatrixSeq(genM, genD, L_, R_, DDi, slr, p, N, B, Vi, R1MatH,
R0PolMatH)
#    Given the generic reduction matrix genM for the current row and block
#    together with its denominator genD
#    and given interval boundaries L_ and R_
#    return the matrix sequences specified by these intervals, i.e.
#    resM_[l] = M_H^{t,\iota}(l) and resD_[l] = "d_H^{t,\iota}(l)"
#
#    NOTE:
#
#    Computations are carried out mod p^N
#    but the result is given mod p^{N+1}
#
    R1Pol = parent(genD)
    R1 = base_ring(R1Pol)

    R0Pol = base_ring(R0PolMatH)
    R0 = base_ring(R0Pol)
    R0PolMat = MatrixSpace(R0Pol, 1, 1)

    tempM_ = LinearRecurrence(transpose(CastMatrix(R0PolMatH,genM)), L_,
                              R_, DDi, slr)
    tempM_ = [ transpose(tempM_[m]) for m in 1:length(tempM_) ]
    tempD_ = LinearRecurrence(transpose(R0PolMat(cast_poly_nmod(R0Pol,genD))),
                               L_, R_, DDi, slr)
    tempD_ = [ transpose(tempD_[m]) for m in 1:length(tempD_) ]
    if (N < B)    # we need to compute the remaining matrices
        if (N == 1)    # everything is congruent mod p
            tempM_ = vcat(tempM_, [ tempM_[1] for l in (N+1):B ])
            tempD_ = vcat(tempD_, [ tempD_[1] for l in (N+1):B ])
        else    # apply the vandermonde trick
                # denominators
            R0Mat = parent(tempD_[1])
            tempD_ = vcat(tempD_, [ zero(R0Mat) for l in (N+1):B ])
            taylor_ = [zero(R0Mat) for l in 1:N]
            for l = 1:N
                for m = 1:N
                    taylor_[l] = taylor_[l] + tempD_[m]*Vi[m,l]
                end
            end
            for l = N+1:B
                tempD_[l] = zero(R0Mat)
                c = 1
                for i = 1:N
                    tempD_[l] = tempD_[l] + taylor_[i]*c
                    c = c*l
                end
            end
            # matrix
            R0Mat = parent(tempM_[1])
            tempM_ = vcat(tempM_, [ zero(R0Mat) for l in (N+1):B ])
            taylor_ = [zero(R0Mat) for l in 1:N]
            for l = 1:N
                for m = 1:N
                    taylor_[l] = taylor_[l] + tempM_[m]*Vi[m,l]
                end
            end
            for l = N+1:B
                tempM_[l] = zero(R0Mat)
                c = 1
                for i = 1:N
                    tempM_[l] = tempM_[l] + taylor_[i]*c
                    c = c*l
                end
            end
        end
    end
    resM_ = [ CastBaseMatrix(R1MatH,tempM_[l]) for l in 1:B ]
    resD_ = [ R1(lift_elem(tempD_[l][1,1])) for l in 1:B ]

    return resM_, resD_
end

function HReduce(i, iota, mu_, genM, genD, M_, D_, p, R1ModH)
# reduces the differential T_{(i,j),k} horizontally
#
    R1 = base_ring(R1ModH)
    b = R1ModH.cols

    res = zero(R1ModH)

    # Note: #mu_ = b*k+1
    res[1,1] = mu_[end]   # Recall: mu_[r] = mu_{k,r+1,j}

    for l = (i+ length(mu_)):-1:1
        for m = 1:b-1
            res *= Evaluate(genM, R1(p*l-m))*inv(evaluate(genD, R1(p*l-m)))
        end
        res *= Evaluate(genM, R1(p*l-b))
        d = evaluate(genD, R1(p*l-b))
        res = R1ModH([ R1(divexact(res[1,m],d)) for m in 1:b ])
        println(">>>>>>>>");
        println(res);
        res *= M_[l]
        res *= inv(D_[l])
        println(res);
        res *= Evaluate(genM, R1((l-1)*p))
        res *= inv(evaluate(genD,R1((l-1)*p)))
        println(res);
        if ((l-1)-i-1 >= 0)
            res[1,1] += mu_[(l-1)-i]
        end
        println(res);
    end

    return res
end

function VRedMatrixSeq(j, a, h, r_, s_, p, N, R1MatV, R1PolMatV)
# Given the data to compute the generic reduction matrix
# (and its denominator) of the iota-th block,
# return the matrix sequences needed for vertical reduction, i.e.
# resM_[k] = M_V^{\iota}(k) and resD_[k] = "d_V^{\iota}(k)"
#
    b = degree(h)
    R1 = base_ring(h)
    R1Pol = parent(h)
    t = gen(R1Pol)
    R1PolMat = MatrixSpace(R1Pol, 1, 1)

    t_ = vcat([ 0 ], [ Row(-p*(a*k + j), a) for k in 0:(N-1) ])
    L_ = [ t_[i] for i in 1:(length(t_)-1) ]
    R_ = [ t_[i] for i in 2:length(t_) ]
    slr = floor(Int64, log(4, R_[end]))
    DDi = UpperCaseDD(one(R1), R1(2^slr), 2^slr)
    DDi = inv(DDi)

    iota = Block(-p*j, a)

    genM = zero(R1PolMatV)
    c_ = [  ] #R1Pol
    for i = 0:b-2
        c_ = [ (a*t + iota-a)*coeff(r_[i+1], m) +
              a*coeff(derivative(s_[i+1]), m) for m in 0:(b-2) ]
        for m = 1:b-1
            genM[i+1,m] = c_[m]
        end
    end
    resM_ = LinearRecurrence(transpose(genM), L_, R_, DDi, slr)
    resM_ = [ transpose(resM_[m]) for m in 1:length(resM_) ]

    genD = R1PolMat(a*t +iota-a)
    tempD_ = LinearRecurrence(transpose(genD), L_, R_, DDi, slr)
    tempD_ = [ transpose(tempD_[m]) for m in 1:length(tempD_) ]
    resD_ = [ tempD_[k][1,1] for k in 1:N ]

    return resM_, resD_
end

function VReduce(i, j, a, h, wH_, M_, D_, R1ModV)
# "vertically" reduces the already
# "horziontally reduced" differential
# w_{(i,j)} = wH_[*,j,i+1]
#
    R1 = base_ring(h)

    b = degree(h)
    N = length(wH_)

    res = R1ModV([ wH_[N][ j][ i+1][1,m] for m in 2:b ])

    for k = (N-1):-1:1
        res *= M_[k+1]
        d = D_[k+1]
        res = R1ModV([ R1(divexact(res[1,m], d)) for m in 1:(b-1) ])
        res = R1ModV([ wH_[k][j][i+1][1,m] + res[1,m-1] for m in 2:b ])
    end

    res *= M_[1]
    res *= inv(D_[1])

    return res
end

#function PFrobeniusAction(a, hbar, N)#(a::RngIntElt, hbar::RngUPolElt, N::RngIntElt)\
#-> AlgMatElt
#
#   Provided for backwards compatibility. Use "AbsoluteFrobeniusAction"
#   instead.
#
#    return AbsoluteFrobeniusAction(a, hbar, N)
#end
function lift_fq_to_qadic(R, a)
    if typeof(a) <: Union{<: ResElem, Nemo.gfp_elem}
        return R(lift_elem(a))
    else
        return R(FmpzPolyRing(:x)([coeff(a, i) for i in 0:degree(R)-1]))
    end
end

function lift_fq_to_qadic_poly(R::PolyRing, f)
    #Ry, _ = PolynomialRing(ResidueRing(ZZ, characteristic(base_ring(parent(f)))^N), "y")
    return R([lift_fq_to_qadic(base_ring(R), coeff(f, i)) for i in 0:degree(f)])
end

function AbsoluteFrobeniusAction(a, hbar,N)#(a::RngIntElt, hbar::RngUPolElt,N::RngIntElt)\
#-> AlgMatElt
#
#   Implements [1, Algorithm 1]

#   INPUT:

#   -  ``a`` - an integer > 1
#   -  ``hbar`` - a squarefree univariate polynomial over a finite field
#                 of degree coprime to a
#   -  ``N`` - an integer > 0 setting the desired precision

#   OUTPUT:

#   A integer matrix modulo p^N representing the action of the
#   absolute Frobenius on the first crystalline cohomology space
#   of the smooth projective model of y^a - hbar = 0.

#   NOTE:

#   The complexity is O( p^(1/2) n MM(g) N^(5/2) + \log(p)ng^4N^4 )
#
    # Step 0: Setup
    K = base_ring(hbar)
    p = convert(Int64,characteristic(K))
    q = order(K)
    n = degree(K)
    b = degree(hbar)

    # Check user input
    #(! IsFinite(K)) && error("The curve must be defined over a finite field.")
    #(! IsSeparable(hbar)) && error("The current implementation only supports squarefree hbar.")
    (gcd(a,b) != 1) && error("The current implementation needs a and the degree of hbar to be coprime.")
    (a < 2) && error("Please enter an integer a > 1.")
    (b < 2) && error("Please enter a polynomial hbar of degree > 1.")
    (N < 1) && error("Please enter a positive precision N")
    (p <= (a*N-1)*b) && error("Characteristic too small", (a*N - 1)*b)

    if n == 1
        if fits(Int64, ZZ(p)^(N+1))
            R0 = ResidueRing(ZZ, p^N)
            R1 = ResidueRing(ZZ, p^(N+1))
        else
            R0 = ResidueRing(ZZ, ZZ(p)^N)
            R1 = ResidueRing(ZZ, ZZ(p)^(N+1))
        end
    else
        R0 = QadicField(p, n, N)
        R1 = QadicField(p, n, N + 1)
    end
    R0Pol,t1 = PolynomialRing(R0,'t')
    R1Pol,t2 = PolynomialRing(R1,'t')

    Rt,t3 = PolynomialRing(ZZ,'t')
    h = lift_fq_to_qadic_poly(R1Pol, hbar)
    println(h)
    println(">>>>>>>>>>>>>>>>>>>>>>")

    # Step 1: Horizontal reduction
    R1MatH = MatrixSpace(R1, b, b)
    R1ModH = MatrixSpace(R1, 1, b)
    R1PolMatH = MatrixSpace(R1Pol, b, b)
    R0PolMatH = MatrixSpace(R0Pol, b, b)

    wH_ = [ [ [] for j in 1:(a-1) ] for k in 0:(N-1) ]
    # stores the results of the reduction
    # wH_[k+1,j,i+1] = w_{(i,j),k}
    # Note: w_{(i,j),k} is nonzero only in the
    # iota(j)-th block, so _only_ this block is stored

    # vandermonde trick: preliminaries
    R0Mat = MatrixSpace(R0, N, N)
    if (N < b-1 +b*(N-1)) && (N > 1)
        V = R0Mat( [ i^j for j in 0:N-1 for i in 1:N ])
        Vi = inv(V)
        if Vi isa Tuple
            Vi = divexact(Vi[1],Vi[2])
        end
    else
        Vi = one(R0Mat)
    end

    hk = one(R1Pol)
    hFrob = R1Pol([ frobenius(coeff(h,i)) for i in 0:degree(h) ])
    # at the start of the k-th loop hk = (hFrob)^k
    for k = 0:(N-1)
        # reduction matrix sequences: preliminaries
        B = b-1 +b*k
        mn = min(N, B)
        L_ = [ (l-1)*p for l in 1:mn ]
        R_ = [ (l*p -b-1) for l in 1:mn ]
        slr = floor(Int64, log(4, R_[end]))
        DDi = UpperCaseDD(one(R0), R0(2^slr), 2^slr)
        DDi = inv(DDi)

        for j = 1:a-1
            # j and k fix the row index
            t = Row(-p*(a*k +j), a)
            # horizontal reductions are performed
            # row by row from "bottom to top"

            #iota = Block(-p*(a*k +j), a)
            # j fixes the block index
            # Note: this really is independent of k!
            iota = Block(-p*j, a)
            # Block(-p*(a*k+j), a) = Block(-p*j, a)
            @assert( -(t*a+iota) == -p*(a*k+j) )

            # generic reduction matrix
            genM, genD = HRedMatrix(t, iota, a, h, R1PolMatH)

            # reduction matrix sequences: evaluation
            M_, D_ = HRedMatrixSeq(genM, genD, L_, R_, DDi, slr,
                                    p, N, B, Vi, R1MatH, R0PolMatH)

            # approximate frobenius action
            mu_ = ScalarCoefficients(j, k, a, hk, p, q, N)
            println("mu")
            println(mu_)

            # reduce
            wH_[k+1][j] = [ HReduce(i, iota, mu_, genM, genD, M_,
                                   D_, p, R1ModH) for i in 0:(b-2) ]
        end
        hk *= hFrob
    end

    # Step 2: Vertical reduction
    R1MatV = MatrixSpace(R1, b-1, b-1)
    R1ModV = MatrixSpace(R1, 1, b-1)
    R1PolMatV = MatrixSpace(R1Pol, b-1, b-1)
    wV_ = [ [] for j in 1:(a-1) ]
    # stores the results of the reduction
    # wV_[j,i+1] = w_{(i,j)}
    # Note: w_{(i,j)} is nonzero only in the
    # iota(j)-th block, so _only_ this block is stored
    # Note: block size is now b-1!
    # (as opposed to b during horizontal reduction)

    # reduction matrix sequences: preliminaries
    # compute the r_i and s_i needed to define the
    # vertical reduction matrices
    r_, s_ = RSCombination(h)

    for j = 1:a-1
        # reduction matrix sequences: evaluation
        M_, D_ = VRedMatrixSeq(j, a, h, r_, s_, p, N,
                                R1MatV, R1PolMatV)

        # reduce
        wV_[j] = [ VReduce(i, j, a, h, wH_, M_, D_, R1ModV) for i in 0:(b-2) ]
    end

    # Step 3: Assemble output
    R0Mat = MatrixSpace(R0, (a-1)*(b-1), (a-1)*(b-1))
    res = zero(R0Mat)
    for j = 1:a-1
        for i = 0:b-2
            for m = 1:b-1
                res[((j-1)*(b-1) +i+1), ((Block(-p*j, a)-1)*(b-1) +m)] = R0(lift_elem(wV_[j][i+1][1,m]))
            end
        end
    end

    return res
end

function ZetaFunction(a, hbar)#(a::RngIntElt, hbar::RngUPolElt)
#
#   Implements [1, Corollary]

#   INPUT:

#   -  ``a`` - an integer > 1
#   -  ``hbar`` - a squarefree univariate polynomial over a
#                 finite field of degree coprime to a

#   OUTPUT:

#   A rational function over QQ
#
    # Step 0: Setup
    p = convert(Int64,characteristic(base_ring(hbar)))
    q = order(base_ring(hbar))
    n = degree(base_ring(hbar))
    g = ((a-1)*(degree(hbar)-1)) >> 1

    # Step 1: Determine needed precision
    bound = n*g/2 + 2*g*log(p,2)
    # N is the first integer strictly larger than bound
    N = floor(Int64, bound+1)

    # Step 2: Determine absolute Frobenius action mod precision
    M = AbsoluteFrobeniusAction(a, hbar, N)

    println(M);
    # Step 3: Determine Frobenius action mod precision
    MM = deepcopy(M)
    for i in 1:n-1
        # Apply Frobenius to MM
        for j = 1:rows(MM)
            for k = 1:cols(MM)
                MM[j, k] = frobenius(MM[j, k])
            end
        end
        # Multiply
        M = M * MM
    end
    println(M);

    # Step 4: Determine L polynomial
    ZPol,t = PolynomialRing(ZZ,"t")
    #CP = charpoly(PolynomialRing(base_ring(M),"t")[1],M::MatElem{RingElem})
    CP = invoke(charpoly, Tuple{Ring, Union{MatElem{Nemo.nmod},Generic.Mat}},  PolynomialRing(base_ring(M),"t")[1], M)
    println(CP)
    Chi = cast_poly_nmod(ZPol, CP)
    L = numerator(t^(2*g)*(Chi)(1//t))
    coeff_ = [ coeff(L, i) for i in 0:(2*g) ]
    prec = ZZ(p)^N
    mid = prec >> 1
    for i = 0:g
        if (coeff_[i+1] > mid)
            coeff_[i+1] = coeff_[i+1]-prec
        end
    end
    for i = 0:g-1
        coeff_[2*g-i+1] = (q^(g-i))*coeff_[i+1]
    end
    L = ZPol(coeff_)

    # Step 5: Output zeta function
    return L // (q*t^2 - (q+1)*t + 1)
end

