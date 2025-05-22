# return the codomain of a random d-isogeny from E0 and the images of the basis points
function RanIso(d::BigInt, global_data::GlobalData, compute_odd_points::Bool=false)
    deg_dim2 = BigInt(1) << ExponentFull
    deg_sec = d * (deg_dim2 - d) * Cofactor
    E0_data = global_data.E0_data
    a24_0 = E0_data.a24_0
    xP0, xQ0, xPQ0 = E0_data.xP2e, E0_data.xQ2e, E0_data.xPQ2e

    # generate the endomorphism
    alpha, _ = FullRepresentInteger(deg_sec)
    while gcd(alpha) % BigInt(3) == 0
        alpha, _ = FullRepresentInteger(deg_sec)
    end
    xP3e = Proj1(E0_data.OddTorsionBases[1][1].X, E0_data.OddTorsionBases[1][1].Z)
    xQ3e = Proj1(E0_data.OddTorsionBases[1][2].X, E0_data.OddTorsionBases[1][2].Z)
    PQ3e = add(E0_data.OddTorsionBases[1][1], -E0_data.OddTorsionBases[1][2], Proj1(E0_data.A0))
    xPQ3e = Proj1(PQ3e.X, PQ3e.Z)
    d_inv = invmod(d*Cofactor, BigInt(1) << ExponentFull)
    xP, xQ, xPQ = action_on_torsion_basis(d_inv*alpha, a24_0, xP0, xQ0, xPQ0, global_data.E0_data)
    
    # compute the C-isogeny
    ker = kernel_generator(xP3e, xQ3e, xPQ3e, a24_0, involution(alpha), FactorForAuxiliaryDegree, ExponentCofactor, global_data.E0_data.Matrices_odd[1])
    a24, (xP, xQ, xPQ) = odd_e_isogeny(a24_0, ker, FactorForAuxiliaryDegree, ExponentCofactor, [xP, xQ, xPQ])
    
    # compute the two-dimensional isogeny
    if compute_odd_points
        a24, xP, xQ, xPQ, odd_images = d2isogeny(a24_0, a24, xP0, xQ0, xPQ0, xP, xQ, xPQ, ExponentFull, d, Proj1{FqFieldElem}[xP3e, xQ3e, xPQ3e], global_data) 
        return a24, xP, xQ, xPQ, odd_images, LeftIdeal(alpha, d)
    else
        a24, xP, xQ, xPQ, _ = d2isogeny(a24_0, a24, xP0, xQ0, xPQ0, xP, xQ, xPQ, ExponentFull, d, Proj1{FqFieldElem}[], global_data) 
        return a24, xP, xQ, xPQ, LeftIdeal(alpha, d)
    end
end

# used in key generation 
# return the codomain of a random d-isogeny from E0 and the images of the basis points
function ImRanIso(d::BigInt, global_data::GlobalData, compute_odd_points::Bool=false)
    half_ExponentFull = div(ExponentFull,2)
    deg_dim2 = BigInt(1) << (ExponentFull - half_ExponentFull)
    deg_sec = d * (deg_dim2 - d) * Cofactor * BigInt(1) << half_ExponentFull
    E0_data = global_data.E0_data
    a24_0 = E0_data.a24_0
    xP0, xQ0, xPQ0 = E0_data.xP2e, E0_data.xQ2e, E0_data.xPQ2e

    # generate the endomorphism
    alpha, _ = FullRepresentInteger(deg_sec)
    while gcd(alpha) != 1
        alpha, _ = FullRepresentInteger(deg_sec)
    end
    xP3e = Proj1(E0_data.OddTorsionBases[1][1].X, E0_data.OddTorsionBases[1][1].Z)
    xQ3e = Proj1(E0_data.OddTorsionBases[1][2].X, E0_data.OddTorsionBases[1][2].Z)
    PQ3e = add(E0_data.OddTorsionBases[1][1], -E0_data.OddTorsionBases[1][2], Proj1(E0_data.A0))
    xPQ3e = Proj1(PQ3e.X, PQ3e.Z)
    d_inv = invmod(d*Cofactor, deg_dim2)
    xP, xQ, xPQ = action_on_torsion_basis(d_inv*alpha, a24_0, xP0, xQ0, xPQ0, global_data.E0_data)
    
    a2, b2 = kernel_coefficients(involution(alpha), 2, half_ExponentFull, global_data.E0_data.Matrices_2e)
    
    if a2 == 1
        ker2 = ladder3pt(b2, xP0, xQ0, xPQ0, a24_0)
    else
        ker2 = ladder3pt(a2, xQ0, xP0, xPQ0, a24_0)
    end
    ker2 = ladder(deg_dim2, ker2, a24_0)
    # compute the C-isogeny
    ker = kernel_generator(xP3e, xQ3e, xPQ3e, a24_0, involution(alpha), FactorForAuxiliaryDegree, ExponentCofactor, global_data.E0_data.Matrices_odd[1])
    a24, (xP, xQ, xPQ, ker2) = odd_e_isogeny(a24_0, ker, FactorForAuxiliaryDegree, ExponentCofactor, [xP, xQ, xPQ, ker2])
    
    # compute the 2^a-isogeny (a\approx p^{1/4})
    even_images = [xP, xQ, xPQ]
    a24, even_images = two_e_iso_balanced(a24, ker2, half_ExponentFull, even_images) 
    xP, xQ, xPQ = even_images[1:3]
    xP1 = ladder(BigInt(1) << half_ExponentFull, xP0, a24_0)
    xQ1 = ladder(BigInt(1) << half_ExponentFull, xQ0, a24_0)
    xPQ1 = ladder(BigInt(1) << half_ExponentFull, xPQ0, a24_0)
    
    # compute the two-dimensional isogeny
    if compute_odd_points
        a24, xP, xQ, xPQ, images = d2isogeny(a24_0, a24, xP1, xQ1, xPQ1, xP, xQ, xPQ, (ExponentFull - half_ExponentFull), d, Proj1{FqFieldElem}[xP0, xQ0, xPQ0, xP3e, xQ3e, xPQ3e], global_data) 
        xP,xQ,xPQ = images[1:3]
        odd_images = images[4:6]
        return a24, xP, xQ, xPQ, odd_images, LeftIdeal(alpha, d)
    else
        a24, xP, xQ, xPQ, _ = d2isogeny(a24_0, a24, xP1, xQ1, xPQ1, xP, xQ, xPQ, (ExponentFull - half_ExponentFull), d, Proj1{FqFieldElem}[xP0, xQ0, xPQ0], global_data) 
        xP,xQ,xPQ = images[1:3]
        return a24, xP, xQ, xPQ, LeftIdeal(alpha, d)
    end
end


# return the codomain of a random d-isogeny from E and the images of (P, Q),
# where P, Q is the image of the fixed basis of E0[Cofactor] under an isogeny corresponding to I
function GenImRanIso(d::BigInt, count::Int, a24::Proj1{T}, xP::Proj1{T}, xQ::Proj1{T}, xPQ::Proj1{T},
    I::LeftIdeal, nI::BigInt, odd_kernels::Vector{Proj1{T}},  odd_images::Vector{Proj1{T}}, global_data::GlobalData) where T <: RingElem
    l = FactorForAuxiliaryDegree    # we assume l = 3
    N = d * ((BigInt(1) << ExponentFull) - d) * Cofactor * Cofactor    
    extra_path = quadratic_residue_symbol(-N, nI) != 1
    if extra_path
        N = div(N, l)
    end
    
    alpha = Quaternion_0

    # make alpha in I + Z s.t. n(alpha) = N
    C, D = EichlerModConstraint(I, nI, Quaternion_1, Quaternion_1, false)
    N_CD = p * (C^2 + D^2)
    N_N_CD = (N * invmod(N_CD, nI)) % nI
    lambda = sqrt_mod(4*N_N_CD, nI)
    tries = KLPT_keygen_number_strong_approx
    found = false
    for _ in 1:10
        alpha, found = FullStrongApproximation(nI, C, D, lambda, 4*N, tries)
        found && break
        tries *= 2
    end
    
    @assert found
    
    if extra_path
        # M = quaternion_to_matrix(alpha, global_data.E0_data.Matrices_2e)
        
        # Compute C-isogenies
        (xPodd, xQodd, xPQodd) = odd_images
        ker1, ker1_dual = kernel_generator_and_for_dual(xPodd, xQodd, xPQodd, a24, alpha, l, ExponentCofactor, global_data.E0_data.Matrices_odd[1])
        ker1 = xTPLe(ker1, a24, 1)
        ker1_dual = xTPLe(ker1_dual, a24, 1)
        a24_1, (xP1, xQ1, xPQ1, ker1_dual) = odd_e_isogeny(a24, ker1, l, ExponentCofactor - 1, [xP, xQ, xPQ, ker1_dual]) 
        ker2 = kernel_generator(xPodd, xQodd, xPQodd, a24, involution(alpha), l, ExponentCofactor, global_data.E0_data.Matrices_odd[1])
        Malpha = quaternion_to_matrix(alpha, global_data.E0_data.Matrices_2e)
        d_inv = invmod(d*(BigInt(3)^(ExponentCofactor)), BigInt(1) << ExponentFull)
        xP2, xQ2, xPQ2 = action_of_matrix(d_inv*Malpha, a24, xP, xQ, xPQ)
        a24_2, (xP2, xQ2, xPQ2) = odd_e_isogeny(a24, ker2, l, ExponentCofactor, [xP2, xQ2, xPQ2])
        odd_kernels = vcat(odd_kernels, ker1_dual)

        # compute the two-dimensional isogeny
        a24, xP, xQ, xPQ, odd_kernels = d2isogeny(a24_1, a24_2, xP1, xQ1, xPQ1, xP2, xQ2, xPQ2, ExponentFull, d, odd_kernels, global_data)
        
        # pullback the auxiliary isogeny
        ker1_dual = odd_kernels[end]
        odd_kernels = odd_kernels[1:end-1]
        odd_kernels = vcat(odd_kernels, [xP, xQ, xPQ])
        ker1_dual = ladder(BigInt(3)^count, ker1_dual, a24)
        a24, odd_kernels = odd_e_isogeny(a24, ker1_dual, l, ExponentCofactor-1-count, odd_kernels)
        d_inv = invmod(BigInt(3)^(ExponentCofactor-1-count), BigInt(1) << ExponentFull)
        for i in 1:length(odd_kernels)
            odd_kernels[i] = ladder(d_inv, odd_kernels[i], a24)
        end
        xP = odd_kernels[end-2]
        xQ = odd_kernels[end-1]
        xPQ = odd_kernels[end]
        odd_kernels = odd_kernels[1:end-3]
    else
        # Compute C-isogenies
        (xPodd, xQodd, xPQodd) = odd_images
        ker1, ker1_dual = kernel_generator_and_for_dual(xPodd, xQodd, xPQodd, a24, alpha, l, ExponentCofactor, global_data.E0_data.Matrices_odd[1])
        a24_1, (xP1, xQ1, xPQ1, ker1_dual) = odd_e_isogeny(a24, ker1, l, ExponentCofactor, [xP, xQ, xPQ, ker1_dual])
        ker2 = kernel_generator(xPodd, xQodd, xPQodd, a24, involution(alpha), l, ExponentCofactor, global_data.E0_data.Matrices_odd[1])
        Malpha = quaternion_to_matrix(alpha, global_data.E0_data.Matrices_2e)
        d_inv = invmod(d*Cofactor, BigInt(1) << ExponentFull)
        xP2, xQ2, xPQ2 = action_of_matrix(d_inv*Malpha, a24, xP, xQ, xPQ)
        a24_2, (xP2, xQ2, xPQ2) = odd_e_isogeny(a24, ker2, l, ExponentCofactor, [xP2, xQ2, xPQ2])
        odd_kernels = vcat(odd_kernels, ker1_dual)

        # compute the two-dimensional isogeny
        a24, xP, xQ, xPQ, odd_kernels = d2isogeny(a24_1, a24_2, xP1, xQ1, xPQ1, xP2, xQ2, xPQ2, ExponentFull, d, odd_kernels, global_data)
        
        # pullback the auxiliary isogeny
        ker1_dual = odd_kernels[end]
        odd_kernels = odd_kernels[1:end-1]
        odd_kernels = vcat(odd_kernels, [xP, xQ, xPQ])
        ker1_dual = ladder(BigInt(3)^count, ker1_dual, a24)
        a24, odd_kernels = odd_e_isogeny(a24, ker1_dual, l, ExponentCofactor-count, odd_kernels)
        d_inv = invmod(BigInt(3)^(ExponentCofactor-count), BigInt(1) << ExponentFull)
        for i in 1:length(odd_kernels)
            odd_kernels[i] = ladder(d_inv, odd_kernels[i], a24)
        end
        xP = odd_kernels[end-2]
        xQ = odd_kernels[end-1]
        xPQ = odd_kernels[end]
        odd_kernels = odd_kernels[1:end-3]
    end
    return a24, xP, xQ, xPQ, odd_kernels
end