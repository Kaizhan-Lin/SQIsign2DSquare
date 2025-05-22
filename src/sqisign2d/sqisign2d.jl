using SHA

# Sample a random ideal of prime norm 2^e for test
function sample_random_ideal_2e(e::Int)
    gamma = Quaternion_1
    while norm(gamma) % BigInt(2)^e != 0
        gamma, found = FullRepresentInteger(BigInt(2)^(Log2p + e))
        !found && continue
        gamma = div(gamma, gcd(gamma))
        if gcd(gamma * (Quaternion_1 - Quaternion_i)) % 2 == 0
            gamma = div(gamma * (Quaternion_1 - Quaternion_i), 2)
        end
    end
    I = LeftIdeal(gamma, BigInt(2)^e)
    a = rand(1:BigInt(2)^(e))
    return pushforward((1 + a) * Quaternion_1 + a * Quaternion_j, I)
end

# return a random prime <= 2^KLPT_secret_key_prime_size and = (l|D) = -1
function random_secret_prime(l::Int)
    B = BigInt(floor(p^(1/4)))
    n = rand(1:B)
    while !is_probable_prime(n) || quadratic_residue_symbol(l, n) != -1
        n = rand(1:B)
    end
    return n
end

# return a random prime in [lB, uB]
function random_prime(lB::BigInt, uB::BigInt)
    n = rand(lB:uB)
    while !is_probable_prime(n)
        n = rand(lB:uB)
    end
    return n
end


function auxiliary_path(a24::Proj1{T}, xP::Proj1{T}, xQ::Proj1{T}, xPQ::Proj1{T}, odd_kernels::Vector{Proj1{T}},
    I::LeftIdeal, nI::BigInt, q::BigInt, odd_images::Vector{Proj1{T}}, global_data::GlobalData) where T <: RingElem
    d = (BigInt(1) << ExponentFull) - q
    d_coprime_to_3 = d
    count = 0
    while d_coprime_to_3 % 3 == 0
        count = count + 1
        d_coprime_to_3 = div(d_coprime_to_3,3) 
    end
    a24aux, xPaux, xQaux, xPQaux, images = GenImRanIso(d_coprime_to_3, count, a24, xP, xQ, xPQ, I, nI, odd_kernels, odd_images, global_data)
    return a24aux, xPaux, xQaux, xPQaux, images
end

function key_gen(global_data::GlobalData)
    D_sec = random_secret_prime(FactorForAuxiliaryDegree)
    a24, xP, xQ, xPQ, odd_images, I_sec = ImRanIso(D_sec, global_data, true)
    a24, images = Montgomery_normalize(a24, vcat([xP, xQ, xPQ], odd_images))
    xP, xQ, xPQ = images[1:3]
    odd_images = images[4:end]
    A = Montgomery_coeff(a24)
    nl = length(global_data.E0_data.DegreesOddTorsionBases)
    Ms = Vector{Matrix{BigInt}}(undef, nl)
    for i in 1:nl
        l, e = global_data.E0_data.DegreesOddTorsionBases[i]
        xPodd, xQodd, xPQodd = torsion_basis(A, l, e)
        xPim, xQim, xPQim = odd_images[3*(i-1)+1:3*i]
        a, b, c, d = bi_dlog_odd_prime_power(A, xPim, xQim, xPQim, xPodd, xQodd, xPQodd, l, e, global_data.E0_data)
        Ms[i] = [a c; b d]
    end
    return Montgomery_coeff(a24), (I_sec, D_sec, xP, xQ, xPQ, odd_images, Ms)
end

function commitment(global_data::GlobalData)
    D_sec = rand(1:BigInt(1) << (ExponentFull))
    while gcd(D_sec, 2*Cofactor) != 1
        D_sec = rand(1:BigInt(1) << (ExponentFull))
    end
    a24, xP, xQ, xPQ, odd_images, I_sec = RanIso(D_sec, global_data, true)
    a24, images = Montgomery_normalize(a24, vcat([xP, xQ, xPQ], odd_images))
    xP, xQ, xPQ = images[1:3]
    odd_images = images[4:end]
    A = Montgomery_coeff(a24)
    nl = length(global_data.E0_data.DegreesOddTorsionBases)
    Ms = Vector{Matrix{BigInt}}(undef, nl)
    l, e = global_data.E0_data.DegreesOddTorsionBases[1]
    xPodd, xQodd, xPQodd = torsion_basis(A, l, e)
    xPim, xQim, xPQim = odd_images[1:3]
    a, b, c, d = bi_dlog_odd_prime_power(A, xPodd, xQodd, xPQodd, xPim, xQim, xPQim, l, e, global_data.E0_data)
    Ms = [a c; b d]
    return A, (I_sec, D_sec, xP, xQ, xPQ, xPodd, xQodd, xPQodd), Ms
end


function challenge(A::FqFieldElem, m::String)
    h = sha3_256(string(A) * m)
    c = BigInt(0)
    len = SQISIGN_challenge_length
    n, r = divrem(len, 8)
    for i in 1:(n+1)
        c += BigInt(h[i]) << (8*(i-1))
    end
    c >>= 8 - r

    return c
end

function signing(pk::FqFieldElem, sk, m::String, global_data::GlobalData, is_compact::Bool=false)
    A = pk
    a24pub = A_to_a24(A)
    Isec, Dsec, xPsec, xQsec, xPQsec, odd_images, M_odd_images = sk
    two_to_a = BigInt(1) << ExponentFull

    while true
        # compute commitment
        Acom, (Icom, Dcom, xPcom, xQcom, xPQcom, xPcom_fix, xQcom_fix, xPQcom_fix), Mcom = commitment(global_data)
        a24com = A_to_a24(Acom)

        # compute challenge and the pull-back of the corresponding ideal
        cha = challenge(Acom, m)
        a, b = Mcom * [1, cha]
        a, b, c, d = global_data.E0_data.Matrix_odd_inv * [b, 0, -a, 0]
        alpha = QOrderElem(a, b, c, d)
        Icha = LeftIdeal(alpha, Cofactor)
        Kcha = ladder3pt(cha, xPcom_fix, xQcom_fix, xPQcom_fix, a24com)
        if !is_compact
            a24cha, (xPcha, xQcha, xPQcha) = odd_e_isogeny(a24com, Kcha, 3, ExponentCofactor, [xPcom, xQcom, xPQcom])
            a24cha, (xPcha, xQcha, xPQcha) = Montgomery_normalize(a24cha, [xPcha, xQcha, xPQcha])
        else
            a24cha, (xPcha, xQcha, xPQcha, Kcha_dual) = odd_e_isogeny(a24com, Kcha, 3, ExponentCofactor, [xPcom, xQcom, xPQcom, xQcom_fix])
            a24cha, (xPcha, xQcha, xPQcha, Kcha_dual) = Montgomery_normalize(a24cha, [xPcha, xQcha, xPQcha, Kcha_dual])
        end
        Acha = Montgomery_coeff(a24cha)

        # find alpha in bar(Isec)IcomIcha suitable for the response
        Icomcha = intersection(Icom, Icha)
        nI = Dsec * Dcom * Cofactor
        J, nJ, alpha, found = element_for_response(Isec, Icomcha, Dsec, Dcom * Cofactor, ExponentFull, FactorForAuxiliaryDegree)
        !found && continue
        
        # compute the image under the response sigma
        Malpha = quaternion_to_matrix(involution(alpha), global_data.E0_data.Matrices_2e)
        DcomCofactor_inv = invmod(Dcom*Cofactor, two_to_a)
        xPres, xQres, xPQres = action_of_matrix(DcomCofactor_inv*Malpha, a24cha, xPcha, xQcha, xPQcha)
        q = div(norm(alpha), nI)
        n_odd_l = length(global_data.E0_data.DegreesOddTorsionBases)
        odd_kernels = Proj1{FqFieldElem}[]
        odd_kernel_coeffs = Tuple{Int, Int}[]
        IsecIsigma = ideal_transform(Icomcha, alpha, Dcom * Cofactor)

        # compute the auxiliary ellitic curve
        a24aux, xPaux, xQaux, xPQaux, odd_images = auxiliary_path(a24pub, xPsec, xQsec, xPQsec, odd_kernels, Isec, Dsec, q, odd_images, global_data)

        Aaux = Montgomery_coeff(a24aux)
        if !is_compact
            # modify xPaux, xQaux, xPQaux to be the images of the fixed torions
            xPfix, xQfix, xPQfix = torsion_basis(Acha, ExponentFull)
            n1, n2, n3, n4 = ec_bi_dlog_response(Acha, xPfix, xQfix, xPQfix, xPres, xQres, xPQres, global_data.E0_data)
            Mres = [n1 n3; n2 n4]
            xPaux, xQaux, xPQaux = action_of_matrix(Mres, a24aux, xPaux, xQaux, xPQaux)
    
            # compress the signature
            sign = Vector{UInt8}(undef, SQISIGN2D_signature_length)
            idx = 1
            Acom_byte = Fq_to_bytes(Acom)
            sign[idx:idx+SQISIGN2D_Fp2_length-1] = Acom_byte
            idx += SQISIGN2D_Fp2_length
            Aaux_byte = Fq_to_bytes(Aaux)
            sign[idx:idx+SQISIGN2D_Fp2_length-1] = Aaux_byte
            idx += SQISIGN2D_Fp2_length

            xPfix, xQfix, xPQfix = torsion_basis(Aaux, ExponentFull)
            n1, n2, n3, n4 = ec_bi_dlog_response(Aaux, xPaux, xQaux, xPQaux, xPfix, xQfix, xPQfix, global_data.E0_data)
            if n1 & 1 == 1
                n1inv = invmod(n1, two_to_a)
                n1d = sqrt_mod_2power(n1^2 % two_to_a, ExponentFull)
                sign[idx] = ((n1d - n1) % two_to_a == 0 || (n1d + n1) % two_to_a == 0) ? 0x02 : 0x00
                idx += 1
                n2 = (n2 * n1inv) % two_to_a
                n3 = (n3 * n1inv) % two_to_a
                n4 = (n4 * n1inv) % two_to_a
                for n in [n2, n3, n4]
                    n_bytes = integer_to_bytes(n, SQISIGN2D_twopower_length)
                    sign[idx:idx+SQISIGN2D_twopower_length-1] = n_bytes
                    idx += SQISIGN2D_twopower_length
                end
            else
                n2inv = invmod(n2, two_to_a)
                n2d = sqrt_mod_2power(n2^2 % two_to_a, ExponentFull)
                sign[idx] = ((n2d - n2) % two_to_a == 0 || (n2d + n2) % two_to_a == 0) ? 0x03 : 0x01
                idx += 1
                n1 = (n1 * n2inv) % two_to_a
                n3 = (n3 * n2inv) % two_to_a
                n4 = (n4 * n2inv) % two_to_a
                for n in [n1, n3, n4]
                    n_bytes = integer_to_bytes(n, SQISIGN2D_twopower_length)
                    sign[idx:idx+SQISIGN2D_twopower_length-1] = n_bytes
                    idx += SQISIGN2D_twopower_length
                end
            end
        else
            eval_points = vcat([xPsec, xQsec, xPQsec], odd_kernels)
            a24mid = a24pub
            xPmid, xQmid, xPQmid = eval_points[1:3]
            a24mid, (xPmid, xQmid, xPQmid) = Montgomery_normalize(a24mid, [xPmid, xQmid, xPQmid])
            Amid = Montgomery_coeff(a24mid)
            xPfix, xQfix, xPQfix = torsion_basis(Amid, ExponentFull)
            n1, n2, n3, n4 = ec_bi_dlog_response(Amid, xPfix, xQfix, xPQfix, xPmid, xQmid, xPQmid, global_data.E0_data)

            a24aux_normal, _ = Montgomery_normalize(a24aux, Proj1{FqFieldElem}[])
            Aaux_normal = Montgomery_coeff(a24aux_normal)
            d2cod_bit = lex_order(Aaux_normal, Acha) ? 0 : 1
            a24aux, xPaux, xQaux, xPQaux, _ = d2isogeny(a24aux, a24cha, xPaux, xQaux, xPQaux, xPres, xQres, xPQres, ExponentFull, q, Proj1{FqFieldElem}[], global_data)
            Aaux = Montgomery_coeff(a24aux)
            xPfix, xQfix, xPQfix = torsion_basis(Aaux, ExponentFull)
            m1, m2, m3, m4 = ec_bi_dlog_response(Aaux, xPaux, xQaux, xPQaux, xPfix, xQfix, xPQfix, global_data.E0_data)
            c = invmod(BigInt(1) << ExponentFull - q, BigInt(1) << ExponentFull)
            M = c * [m1 m3; m2 m4] * [n1 n3; n2 n4]

            # compress the signature
            sign = Vector{UInt8}(undef, CompactSQISIGN2D_signature_length)
            idx = 1
            Aaux_byte = Fq_to_bytes(Aaux)
            sign[idx:idx+SQISIGN2D_Fp2_length-1] = Aaux_byte
            idx += SQISIGN2D_Fp2_length

            n1, n2, n3, n4 = M
            if n1 & 1 == 1
                n1inv = invmod(n1, two_to_a)
                n1d = sqrt_mod_2power(n1^2 % two_to_a, ExponentFull)
                sign[idx] = ((n1d - n1) % two_to_a == 0 || (n1d + n1) % two_to_a == 0) ? 0x02 : 0x00
                idx += 1
                n2 = (n2 * n1inv) % two_to_a
                n3 = (n3 * n1inv) % two_to_a
                n4 = (n4 * n1inv) % two_to_a
                for n in [n2, n3, n4]
                    n_bytes = integer_to_bytes(n, SQISIGN2D_twopower_length)
                    sign[idx:idx+SQISIGN2D_twopower_length-1] = n_bytes
                    idx += SQISIGN2D_twopower_length
                end
            else
                n2inv = invmod(n2, two_to_a)
                n2d = sqrt_mod_2power(n2^2 % two_to_a, ExponentFull)
                sign[idx] = ((n2d - n2) % two_to_a == 0 || (n2d + n2) % two_to_a == 0) ? 0x03 : 0x01
                idx += 1
                n1 = (n1 * n2inv) % two_to_a
                n3 = (n3 * n2inv) % two_to_a
                n4 = (n4 * n2inv) % two_to_a
                for n in [n1, n3, n4]
                    n_bytes = integer_to_bytes(n, SQISIGN2D_twopower_length)
                    sign[idx:idx+SQISIGN2D_twopower_length-1] = n_bytes
                    idx += SQISIGN2D_twopower_length
                end
            end

            xPcha, xQcha, xPQcha = torsion_basis(Acha, FactorForAuxiliaryDegree, ExponentCofactor)
            a, b = bi_dlog_challenge(Acha, Kcha_dual, xPcha, xQcha, xPQcha, global_data.E0_data)
            if a % FactorForAuxiliaryDegree != 0
                b = (b * invmod(a, Cofactor)) % Cofactor
                if b < 0
                    b += Cofactor
                end
                sign[idx] = 1
                sign[idx+1:idx+SQISIGN2D_cofactor_length] = integer_to_bytes(b, SQISIGN2D_cofactor_length)
                P = xQcha
            else
                a = (a * invmod(b, Cofactor)) % Cofactor
                if a < 0
                    a += Cofactor
                end
                sign[idx] = 0
                sign[idx+1:idx+SQISIGN2D_cofactor_length] = integer_to_bytes(a, SQISIGN2D_cofactor_length)
                P = xPcha
            end
            idx += SQISIGN2D_cofactor_length + 1
            a24com_d, tmp = odd_e_isogeny(a24cha, Kcha_dual, FactorForAuxiliaryDegree, ExponentCofactor, [P])
            a24com_d, tmp = Montgomery_normalize(a24com_d, [tmp[1]])
            Kcha_d = tmp[1]
            r = ec_dlog(Acom, Kcha, Kcha_d, xQcom_fix, global_data.E0_data)
            sign[idx:idx+SQISIGN2D_cofactor_length-1] = integer_to_bytes(r, SQISIGN2D_cofactor_length)
            idx += SQISIGN2D_cofactor_length

            sign[idx] = d2cod_bit
            idx += 1
        end
        return sign
    end
end


function verify(pk::FqFieldElem, sign::Vector{UInt8}, m::String, global_data::GlobalData)
    # decompress the signature
    idx = 1
    Acom = bytes_to_Fq(sign[idx:idx+SQISIGN2D_Fp2_length-1], global_data.Fp2)
    a24com = A_to_a24(Acom)
    idx += SQISIGN2D_Fp2_length
    Aaux = bytes_to_Fq(sign[idx:idx+SQISIGN2D_Fp2_length-1], global_data.Fp2)
    a24aux = A_to_a24(Aaux)
    idx += SQISIGN2D_Fp2_length
    is_n1_odd = sign[idx] & 1 == 0x00
    is_adjust_sqrt = sign[idx] & 2 == 0x00
    idx += 1
    n = Vector{BigInt}(undef, 3)
    for i in 1:3
        n[i] = bytes_to_integer(sign[idx:idx+SQISIGN2D_twopower_length-1])
        idx += SQISIGN2D_twopower_length
    end
    if is_n1_odd
        n1, n2, n3, n4 = 1, n[1], n[2], n[3]
    else
        n1, n2, n3, n4 = n[1], 1, n[2], n[3]
    end
    xPfix, xQfix, xPQfix = torsion_basis(Aaux, ExponentFull)
    xPaux = linear_comb_2_e(n1, n2, xPfix, xQfix, xPQfix, a24aux, ExponentFull)
    xQaux = linear_comb_2_e(n3, n4, xPfix, xQfix, xPQfix, a24aux, ExponentFull)
    xPQaux = linear_comb_2_e(n1 - n3, n2 - n4, xPfix, xQfix, xPQfix, a24aux, ExponentFull)

    a24com = A_to_a24(Acom)
    a24aux = A_to_a24(Aaux)
    a24pub = A_to_a24(pk)

    c = challenge(Acom, m)
    xPcom, xQcom, xPQcom = torsion_basis(Acom, FactorForAuxiliaryDegree, ExponentCofactor)
    Kcha = ladder3pt(c, xPcom, xQcom, xPQcom, a24com)
    a24cha, _ = odd_e_isogeny(a24com, Kcha, FactorForAuxiliaryDegree, ExponentCofactor, Proj1{FqFieldElem}[])
    a24cha, _ = Montgomery_normalize(a24cha, Proj1{FqFieldElem}[])
    Acha = Montgomery_coeff(a24cha)
    xPres, xQres, xPQres = torsion_basis(Acha, ExponentFull)

    # adjust <(Pcha, Paux), (Qcha, Qaux)> to be isotropic w.r.t. the Weil pairing
    two_to_a = BigInt(1) << ExponentFull
    w_aux = Weil_pairing_2power(Aaux, xPaux, xQaux, xPQaux, ExponentFull)
    w_res = Weil_pairing_2power(Acha, xPres, xQres, xPQres, ExponentFull)
    e_aux = fq_dlog_power_of_2_opt(w_aux, global_data.E0_data.dlog_data_res)
    e_res = fq_dlog_power_of_2_opt(w_res, global_data.E0_data.dlog_data_res)
    e = e_res * invmod(-e_aux, two_to_a) % two_to_a
    ed = sqrt_mod_2power(e, ExponentFull)
    is_adjust_sqrt && (ed += two_to_a >> 1)
    xPaux = ladder(ed, xPaux, a24aux)
    xQaux = ladder(ed, xQaux, a24aux)
    xPQaux = ladder(ed, xPQaux, a24aux)

    # isogeny of dimension 2
    Es, xPtest, xQtest, xPQtest = d2isogeny_verify(a24cha, a24aux, xPres, xQres, xPQres, xPaux, xQaux, xPQaux, ExponentFull, global_data)
    j0 = jInvariant_a24(a24pub)
    j1 = jInvariant_A(Es[1])
    j2 = jInvariant_A(Es[2])
    # test the response degree
    a24test = A_to_a24(Es[1])
    w_test = Weil_pairing_2power(Montgomery_coeff(a24test), xPtest, xQtest, xPQtest, ExponentFull)
    e_test = fq_dlog_power_of_2(w_test, w_res, ExponentFull)
    if j1 == j0
        return e_test % 3 != 0
        # return true
    elseif j2 == j0
        return (BigInt(2)^ExponentFull - e_test) % 3 != 0
        # return true
    else
        print("here")
        return false
    end
    # return j1 == j0 || j2 == j0
end


function verify_compact(pk::FqFieldElem, sign::Vector{UInt8}, m::String, global_data::GlobalData)
    # decompress the signature
    idx = 1
    Aaux = bytes_to_Fq(sign[idx:idx+SQISIGN2D_Fp2_length-1], global_data.Fp2)
    idx += SQISIGN2D_Fp2_length
    is_n1_odd = sign[idx] & 1 == 0x00
    is_adjust_sqrt = sign[idx] & 2 == 0x00
    idx += 1
    n = Vector{BigInt}(undef, 3)
    for i in 1:3
        n[i] = bytes_to_integer(sign[idx:idx+SQISIGN2D_twopower_length-1])
        idx += SQISIGN2D_twopower_length
    end
    if is_n1_odd
        n1, n2, n3, n4 = 1, n[1], n[2], n[3]
    else
        n1, n2, n3, n4 = n[1], 1, n[2], n[3]
    end
    xPfix, xQfix, xPQfix = torsion_basis(Aaux, ExponentFull)
    a24aux = A_to_a24(Aaux)
    xPaux = linear_comb_2_e(n1, n2, xPfix, xQfix, xPQfix, a24aux, ExponentFull)
    xQaux = linear_comb_2_e(n3, n4, xPfix, xQfix, xPQfix, a24aux, ExponentFull)
    xPQaux = linear_comb_2_e(n1- n3, n2 - n4, xPfix, xQfix, xPQfix, a24aux, ExponentFull)

    bit_s = sign[idx]
    idx += 1
    s = bytes_to_integer(sign[idx:idx+SQISIGN2D_cofactor_length-1])
    idx += SQISIGN2D_cofactor_length
    r = bytes_to_integer(sign[idx:idx+SQISIGN2D_cofactor_length-1])
    idx += SQISIGN2D_cofactor_length
    d2cod_bit = sign[idx]
    idx += 1

    n_odd_l = length(global_data.E0_data.DegreesOddTorsionBases)
    odd_kernel_coeffs = Vector{Tuple{Int, Int}}(undef, n_odd_l)

    a24pub = A_to_a24(pk)

    # isogeny of dimension 1
    n_odd_l = length(global_data.E0_data.DegreesOddTorsionBases)
    odd_isog_kers = Proj1{FqFieldElem}[]
    odd_isog_degrees = Tuple{Int, Int}[]
    a24mid = a24pub

    a24mid, _ = Montgomery_normalize(a24mid, Proj1{FqFieldElem}[])
    Amid = Montgomery_coeff(a24mid)
    xPmid, xQmid, xPQmid = torsion_basis(Amid, ExponentFull)

    # adjust <(Pmid, Pmid), (Qpub, Qaux)> to be isotropic w.r.t. the Weil pairing
    two_to_a = BigInt(1) << ExponentFull
    w_aux = Weil_pairing_2power(Aaux, xPaux, xQaux, xPQaux, ExponentFull)
    w_mid = Weil_pairing_2power(Amid, xPmid, xQmid, xPQmid, ExponentFull)
    e_aux = fq_dlog_power_of_2_opt(w_aux, global_data.E0_data.dlog_data_res)
    e_mid = fq_dlog_power_of_2_opt(w_mid, global_data.E0_data.dlog_data_res)
    e = e_mid * invmod(-e_aux, two_to_a) % two_to_a
    ed = sqrt_mod_2power(e, ExponentFull)
    is_adjust_sqrt && (ed += two_to_a >> 1)
    xPaux = ladder(ed, xPaux, a24aux)
    xQaux = ladder(ed, xQaux, a24aux)
    xPQaux = ladder(ed, xPQaux, a24aux)

    # isogeny of dimension 2
    Es, xPtest, xQtest, xPQtest = d2isogeny_verify(a24mid, a24aux, xPmid, xQmid, xPQmid, xPaux, xQaux, xPQaux, ExponentFull, global_data)
    A1, (xPtest, xQtest, xPQtest) = Montgomery_normalize(A_to_a24(Es[1]), [xPtest, xQtest, xPQtest])
    A2, _ = Montgomery_normalize(A_to_a24(Es[2]), Proj1{FqFieldElem}[])
    A1 = Montgomery_coeff(A1)
    A2 = Montgomery_coeff(A2)
    w_test = Weil_pairing_2power(A1, xPtest, xQtest, xPQtest, ExponentFull)
    e_test = fq_dlog_power_of_2(w_test, w_mid, ExponentFull)
    !lex_order(A1, A2) && ((A1, A2) = (A2, A1))
    if d2cod_bit == 1
        Acha = A1
    else
        Acha = A2
    end
    a24cha = A_to_a24(Acha)
    xPcha, xQcha, xPQcha = torsion_basis(Acha, FactorForAuxiliaryDegree, ExponentCofactor)
    if bit_s == 1
        Kcha_dual = ladder3pt(s, xPcha, xQcha, xPQcha, a24cha)
        P = xQcha
    else
        Kcha_dual = ladder3pt(s, xQcha, xPcha, xPQcha, a24cha)
        P = xPcha
    end
    a24com, tmp = odd_e_isogeny(a24cha, Kcha_dual, FactorForAuxiliaryDegree, ExponentCofactor, [P])
    a24com, tmp = Montgomery_normalize(a24com, [tmp[1]])
    Kcha_d = tmp[1]
    Acom = Montgomery_coeff(a24com)
    c = challenge(Acom, m)
    xPcom, xQcom, xPQcom = torsion_basis(Acom, FactorForAuxiliaryDegree, ExponentCofactor)
    Kcha = ladder3pt(c, xPcom, xQcom, xPQcom, a24com)

    if Kcha == ladder(r, Kcha_d, a24com)    
        j0 = jInvariant_a24(a24cha)
        j1 = jInvariant_A(Es[1])
        j2 = jInvariant_A(Es[2])
        # test the response degree
        if j1 == j0
           return e_test % 3 != 0
            # return true
        elseif j2 == j0
            return (BigInt(2)^ExponentFull - e_test) % 3 != 0
            # return true
        else
            return false
        end
    else
        return  false
    end
end