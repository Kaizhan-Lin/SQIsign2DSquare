# left ideal of the maximal order <1, i, (i + j)/2, (1 + ij)/2>
struct LeftIdeal
    b1::QOrderElem
    b2::QOrderElem
    b3::QOrderElem
    b4::QOrderElem
end

function Base.getindex(I::LeftIdeal, i::Integer)
    if i == 1
        return I.b1
    elseif i == 2
        return I.b2
    elseif i == 3
        return I.b3
    elseif i == 4
        return I.b4
    else
        throw(BoundsError(I, i))
    end
end

function Base.:(==)(I1::LeftIdeal, I2::LeftIdeal)
    return is_subset(I1, I2) && is_subset(I2, I1)
end

function LeftIdeal(basis::Vector{QOrderElem})
    return LeftIdeal(basis[1], basis[2], basis[3], basis[4])
end

function Base.:*(x::QOrderElem, I::LeftIdeal)
    return LeftIdeal(x*I.b1, x*I.b2, x*I.b3, x*I.b4)
end

function Base.:*(I::LeftIdeal, x::QOrderElem)
    return LeftIdeal(I.b1*x, I.b2*x, I.b3*x, I.b4*x)
end

function Base.gcd(I::LeftIdeal)
    return gcd(gcd(I.b1), gcd(I.b2), gcd(I.b3), gcd(I.b4))
end

function Base.div(I::LeftIdeal, a::Integer)
    return LeftIdeal(div(I.b1, a), div(I.b2, a), div(I.b3, a), div(I.b4, a))
end

function ideal_to_matrix(I::LeftIdeal)
    return hcat([[b[i] for i in 1:4] for b in [I.b1, I.b2, I.b3, I.b4]]...)
end

function norm(I::LeftIdeal)
    D = det(ideal_to_matrix(I))
    return integer_square_root(abs(D))
end

# left O-ideal Ox + ON
function LeftIdeal(x::QOrderElem, N::Integer)
    basis = [QOrderElem(1,0,0,0), QOrderElem(0,1,0,0), QOrderElem(0,0,1,0), QOrderElem(0,0,0,1)]
    Ox = [[(b*x)[i] for i in 1:4] for b in basis]
    N = BigInt(N)
    ON = [[N,0,0,0],[0,N,0,0],[0,0,N,0],[0,0,0,N]]
    basis = get_basis(vcat(Ox, ON))
    return LeftIdeal([QOrderElem(b[1], b[2], b[3], b[4]) for b in basis])
end

# left O-ideal I + ON
function larger_ideal(I::LeftIdeal, N::Integer)
    N = BigInt(N)
    ON = [[N,0,0,0],[0,N,0,0],[0,0,N,0],[0,0,0,N]]
    Ibasis = [[b[i] for i in 1:4] for b in [I.b1, I.b2, I.b3, I.b4]]
    basis = get_basis(vcat(Ibasis, ON))
    return LeftIdeal([QOrderElem(b[1], b[2], b[3], b[4]) for b in basis])
end

# return alpha in I s.t. q_I(alpha) is odd and divisible by l,
# q_I(alpha) < 2^a
function element_for_response(Isec::LeftIdeal, I::LeftIdeal, nIsec::BigInt, nI::BigInt, a::Int, l::Int)
    counter = 0
    found = false
    J = LeftIdeal([Quaternion_0, Quaternion_0, Quaternion_0, Quaternion_0])
    nJ = 0
    N = nIsec * nI

    # compute \bar(Isec)I
    invIsecI = involution_product(Isec, I)

    # LLL reduction
    Imatrix = ideal_to_matrix(invIsecI)
    q(x, y) = quadratic_form(QOrderElem(x), QOrderElem(y))
    H = integral_LLL([Imatrix[:, i] for i in 1:4], q)
    LLLmat = Imatrix * H
    red_basis = [LLLmat[:, i] for i in 1:4]

    beta = Quaternion_0
    while !found && counter < KLPT_equiv_num_iter
        counter += 1
        c1, c2, c3, c4 = [rand(-KLPT_equiv_bound_coeff:KLPT_equiv_bound_coeff) for _ in 1:4]
        beta = c1 * red_basis[1] + c2 * red_basis[2] + c3 * red_basis[3] + c4 * red_basis[4]
        beta = QOrderElem(beta)
        nJ = div(norm(beta), N)
        if gcd(beta) == 1
            if nJ % FactorForAuxiliaryDegree != 0 && nJ % 2 == 1 && nJ < BigInt(1) << ExponentFull
                found = true
                J = ideal_transform(I, beta, nI) # Isec * L
                J = larger_ideal(J, nJ) # [Isec]^* L
            end
        end
    end
    return J, nJ, beta, found
end


# return coefficients q_i,j s.t. Nrd(x) = sum_i q_i,i*(x_i + sum_j q_i,j*x_j)^2, where x = sum_i x_iI[i].
# See p.103 in H. Cohen, A Course in Computational Algebraic Number Theory.
function make_quadratic_form_coeffs(basis::Vector{Vector{T}}, quadratic_form::Function) where T <: Integer
    n = length(basis)
    C = zeros(Rational{T}, n, n)
    q = zeros(Rational{T}, n, n)

    for i in 1:n
        C[i, i] = quadratic_form(basis[i], basis[i])
        for j in i+1:n
            C[i, j] = quadratic_form(basis[i], basis[j])
        end
    end

    for i in 1:n
        q[i, i] = C[i, i] - (i > 1 ? sum([q[j, j] * q[j, i]^2 for j in 1:i-1]) : 0)
        for j in i+1:n
            q[i, j] = (2*C[i, j] - 2*sum([q[k,k]*q[k,i]*q[k,j] for k in 1:i])) / (2*q[i, i])
        end
    end
    return q
end

# Return a primitive element in I
function primitive_element(I::LeftIdeal)
    a = I[1]
    i = 1
    while gcd(a) != 1
        a += I[i]
        i = (i % 4) + 1
    end
    return a
end

# a in I s.t. a/l not in O0 for any l | n
function element_prime_to(I::LeftIdeal, n::Integer)
    a = I[1]
    i = 1
    while gcd(gcd(a), n) != 1
        a += I[i]
        i = (i % 4) + 1
    end
    return a
end

# I * bar(beta) / N
function ideal_transform(I::LeftIdeal, beta::QOrderElem, N::BigInt)
    return div(I*involution(beta), N)
end

# x in I
function isin(x::QOrderElem, I::LeftIdeal)
    return gcd(I * involution(x)) % norm(I) == 0
end

# O_0 * I \subset I
function valid_ideal(I::LeftIdeal)
    for b in [I.b1, I.b2, I.b3, I.b4]
        for Ob in [[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]]
            !isin(QOrderElem(Ob) * b, I) && return false
        end
    end
    return true
end

# I1 \subset I2
function is_subset(I1::LeftIdeal, I2::LeftIdeal)
    for b in [I1.b1, I1.b2, I1.b3, I1.b4]
        !isin(b, I2) && return false
    end
    return true
end

# I1 \cap I2 s.t. gcd(norm(I1), norm(I2)) = 1
function intersection(I1::LeftIdeal, I2::LeftIdeal)
    N1 = norm(I1)
    N2 = norm(I2)
    I1N2 = I1 * QOrderElem(N2)
    I2N1 = I2 * QOrderElem(N1)
    gens = [I1N2.b1, I1N2.b2, I1N2.b3, I1N2.b4, I2N1.b1, I2N1.b2, I2N1.b3, I2N1.b4]
    bs = get_basis([[b[i] for i in 1:4] for b in gens])
    return LeftIdeal([QOrderElem(b) for b in bs])
end

# [alpha]*I, computed by (I \cap O0*alpha) * alpha^-1
function pushforward(alpha::QOrderElem, I::LeftIdeal)
    Na = norm(alpha)
    Oalpha = LeftIdeal(alpha, Na)
    L = intersection(I, Oalpha) 
    return ideal_transform(L, alpha, Na)
end

# return \bar(I) * J, a left ideal of the right order of I
function involution_product(I::LeftIdeal, J::LeftIdeal)
    invI = [involution(b) for b in [I.b1, I.b2, I.b3, I.b4]]
    generator = [x * y for x in invI for y in [J.b1, J.b2, J.b3, J.b4]]
    basis = get_basis([to_vector(b) for b in generator])
    return LeftIdeal([QOrderElem(b[1], b[2], b[3], b[4]) for b in basis])
end
