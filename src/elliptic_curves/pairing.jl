export Weil_pairing_2power, Tate_pairing_P0, Tate_pairing_iP0, make_pairing_table, Tate_pairings

# Miller function f_{2^e,P}(Q)
function Miller_function_double(A::T, P::Point{T}, Q::Point{T}, e::Integer) where T <: RingElem
    F = parent(A)
    X, Y, Z = P.X, P.Y, P.Z
    f1, f2 = F(1), F(1)
    for i in 1:e-1
        AZ = A*Z
        QXZ = Q.X*Z
        QZX = Q.Z*X
        QZY = Q.Z*Y
        QZZ = Q.Z*Z
        lam1 = (3*X + 2*AZ) * X + Z^2
        lam12Z = lam1^2*Z
        lam2 = 2*Y*Z
        lam22 = lam2^2
        h1 = lam22 * (Q.Y*Z - QZY) - lam1*lam2 * (QXZ - QZX)
        h2 = lam22 * (QXZ + 2*QZX + A*QZZ) - lam12Z*Q.Z
        f1 = f1^2 * h1
        f2 = f2^2 * h2
        if i < e-1
            lam23 = lam2^3
            X, Y, Z = lam12Z*lam2 - lam23*(AZ + 2*X),
                lam1 * (lam22 * (3*X + AZ) - lam12Z) - Y * lam23,
                Z * lam23
        else
            X, Z = lam1^2*Z - lam22*(AZ + 2*X), Z * lam22
        end
    end
    f1 = f1^2 * (Q.X * Z - Q.Z * X)
    f2 = f2^2 * Q.Z * Z
    return f1, f2
end


function triple(X1::T,Y1::T,Z1::T,a::T) where T <: RingElem
    XX = X1^2
    YY = Y1^2
    ZZ = Z1^2
    YYYY = YY^2
    t0 = ZZ^2
    t1 = a*t0
    t2 = 3*XX
    M = t2+t1
    MM = M^2
    t3 = X1+YY
    t4 = t3^2
    t5 = t4-XX
    t6 = t5-YYYY
    t7 = 6*t6
    E = t7-MM
    EE = E^2
    TT = 16*YYYY
    t8 = M+E
    t9 = t8^2
    t10 = t9-MM
    t11 = t10-EE
    U = t11-TT
    t12 = YY*U
    t13 = 4*t12
    t14 = X1*EE
    t15 = t14-t13
    X3 = 4*t15
    t16 = TT-U
    t17 = E*EE
    t18 = U*t16
    t19 = t18-t17
    t20 = Y1*t19
    Y3 = 8*t20
    t21 = Z1+E
    t22 = t21^2
    t23 = t22-ZZ
    Z3 = t23-EE
    U = -(U-M*E)
    return X3,Y3,Z3,E,U,M,ZZ
end

function Tate_pairing_3power(A::T, P::Point{T}, Q::Point{T}, e::Integer) where T <: RingElem
    F = parent(A)
    f = F(1)
    X, Y, Z = Q.X, Q.Y, Q.Z
    X = X/Z
    Y = Y/Z
    Z = F(1)
    x, y, z = P.X, P.Y, P.Z
    x = x * z
    y = y * z
    y = y * z
    A_div_3 = A/F(3)
    X = X + A_div_3
    x = x + A_div_3 * z^2
    WA = F(1) - A * A_div_3 
    for i in 1:e-1
        x3,y3,z3,tmpe,tmpu,tmpm,tmpz = triple(x,y,z,WA)
        ff = tmpe*(z^2*X-x)*((tmpm*(z^2*X-x)-2*y*(z^3*Y-y)))
        f = f^3 * ff
        f = f * Frob((-tmpu*z^2*(z^2*X-x)-2*y*tmpe*z^2*(z^3*Y+y)))
        x = x3
        y = y3
        z = z3
    end
    t1 = (3*x^2+WA*z^4)/(2*y*z)
    t2 = t1*(X-(x/z^2))
    t3 = t2 - Y + (y/z^3)
    f = f^3*t3
    f = f^(p-1)
    f = f^(div((p+1),Cofactor))
    if f == 0
        f = 1
    end
    return f
end

# Weil pairing e_{2^e}(P, Q)
function Weil_pairing_2power(A::T, P::Point{T}, Q::Point{T}, e::Integer) where T <: RingElem
    fPQ1, fPQ2 = Miller_function_double(A, P, Q, e)
    if fPQ1 == 0 || fPQ2 == 0
        return parent(A)(1)
    end
    fQP1, fQP2 = Miller_function_double(A, Q, P, e)
    return (fPQ1*fQP2) / (fPQ2*fQP1)
end

# Weil pairng e_{2^e}(P, Q)
function Weil_pairing_2power(A::T, xP::Proj1{T}, xQ::Proj1{T}, xPQ::Proj1{T}, e::Integer) where T <: RingElem
    P = Point(A, xP)
    Q = Point(A, xQ)
    PQ = add(P, -Q, Proj1(A))
    if !(xPQ == Proj1(PQ.X, PQ.Z))
        Q = -Q
    end
    return Weil_pairing_2power(A, P, Q, e)
end

# precomputed table for Tate pairings
function make_pairing_table(A::FqFieldElem, P::Point{FqFieldElem}, e::Integer)
    R = P
    x, y = R.X/R.Z, R.Y/R.Z
    table = [[x, y, parent(A)(0)]]
    for i in 1:e-1
        lam = (3*x^2 + 2*A*x + 1) / (2*y)
        R = double(R, Proj1(A))
        x = R.X/R.Z
        y = R.Y/R.Z
        push!(table, [x, y, lam])
    end
    return table
end

# Tate pairing t_{2^e}(P0, P) using precomputed table for P0
function Tate_pairing_P0(P::Point{FqFieldElem}, table::Vector{Vector{FqFieldElem}}, f::Integer)
    x, y, z = P.X, P.Y, P.Z
    x_frob = Frob(x)
    z_frob = Frob(z)
    x0, y0 = table[1][1], table[1][2]
    f0 = 1
    h0 = 1
    for (xt, yt, lam) in table[2:end]
        t0 = x - x0 * z
        t1 = y - y0 * z
        t0 *= lam
        g = t0 - t1
        h = x_frob - Frob(xt) * z_frob
        g *= h
        f0 = f0^2 * g
        h0 = h0^2 * z * z_frob
        x0, y0 = xt, yt
    end
    g = x - x0 * z
    f0 = f0^2 * g
    h0 = h0^2 * z
    f0 = Frob(f0) * h0 / (f0 * Frob(h0))
    f0 = f0^f
    return f0
end

# Tate pairing t_{2^e}(iP0, P) using precomputed table for P0
function Tate_pairing_iP0(P::Point{FqFieldElem}, table::Vector{Vector{FqFieldElem}}, f::Integer)
    x, y, z = P.X, P.Y, P.Z
    x_frob = Frob(x)
    z_frob = Frob(z)
    x0, y0 = table[1][1], table[1][2]
    f0 = 1
    h0 = 1
    for (xt, yt, lam) in table[2:end]
        t0 = x + x0 * z
        t1 = y - mult_by_i(y0) * z
        t0 *= -mult_by_i(lam)
        g = t0 - t1
        h = x_frob + Frob(xt) * z_frob
        g *= h
        f0 = f0^2 * g
        h0 = h0^2 * z * z_frob
        x0, y0 = xt, yt
    end
    g = x + x0 * z
    f0 = f0^2 * g
    h0 = h0^2 * z
    f0 = Frob(f0) * h0 / (f0 * Frob(h0))
    f0 = f0^f
    return f0
end
