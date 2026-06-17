import hashlib
import random
from ecdsa import SECP256k1
from ecdsa.ellipticcurve import Point, INFINITY
import time

class SystemParameters:
    def __init__(self):
        self.curve = SECP256k1.curve
        self.G = SECP256k1.generator
        self.q = SECP256k1.order
        self.p = self.curve.p()
        self.a = self.curve.a()
        self.b = self.curve.b()
        
        self.L_registry = []
        self.SIDs = ["SID_PROJECT_A", "SID_PROJECT_B"]
        self.n_min = 3
        
        self.S_net = random.randint(1, self.q - 1)
        self.P_net = self.S_net * self.G
# Setup functions
def point_to_str(pt):
    if pt == INFINITY:
        return "INFINITY"
    return f"{pt.x()},{pt.y()}"

def sub_points(P1, P2, q):
    return P1 + ((q - 1) * P2)

def hash_func(q, *args):
    hasher = hashlib.sha256()
    
    def update_hash(item):
        if hasattr(item, 'x') and hasattr(item, 'y'):
            hasher.update(point_to_str(item).encode('utf-8'))
        elif isinstance(item, (list, tuple)):
            for sub_item in item:
                update_hash(sub_item)
        else:
            hasher.update(str(item).encode('utf-8'))
            
    for arg in args:
        update_hash(arg)
        
    return int.from_bytes(hasher.digest(), byteorder='big') % q

def hash_to_point(P, SID, curve, p, a, b):
    ctr = 0
    while True:
        hasher = hashlib.sha256()
        hasher.update(point_to_str(P).encode('utf-8'))
        hasher.update(str(SID).encode('utf-8'))
        hasher.update(str(ctr).encode('utf-8'))
        
        x_cand = int.from_bytes(hasher.digest(), byteorder='big') % p
        y_sq = (pow(x_cand, 3, p) + (a * x_cand) + b) % p
        
        if pow(y_sq, (p - 1) // 2, p) == 1:
            y = pow(y_sq, (p + 1) // 4, p)
            try:
                pt = Point(curve, x_cand, y)
                return pt
            except ValueError:
                pass
        ctr += 1
def generate_shares(S_net, N, k, q):
    coefficients = [S_net] + [random.randint(1, q - 1) for _ in range(k - 1)]
    
    shares = []
    # Public indices omega_j = j for simplicity
    for j in range(1, N + 1):
        x = j
        y = 0
        for power, coeff in enumerate(coefficients):
            y = (y + coeff * pow(x, power, q)) % q
        shares.append({'omega': x, 'S_net_j': y})
        
    return shares

def sub_points(P1, P2, q):
    return P1 + ((q - 1) * P2)

# --- Algorithm 1: Sign  ---
def sign(m, S_s, L, SID, PP):
    P_s = S_s * PP.G
    
    if (P_s not in L) or (L not in PP.L_registry) or (SID not in PP.SIDs) or (len(L) < PP.n_min):
        return None
        
    H_p_val = hash_to_point(P_s, SID, PP.curve, PP.p, PP.a, PP.b)
    I_scope = S_s * H_p_val
    
    r = random.randint(1, PP.q - 1)
    r_dean = random.randint(1, PP.q - 1)
    r_z = random.randint(1, PP.q - 1)
    
    C_1 = r_dean * PP.G
    C_2 = P_s + (r_dean * PP.P_net)
    
    L_s = r * PP.G
    R_s = r * H_p_val
    A_s = r_z * PP.G
    B_s = r_z * PP.P_net
    
    n = len(L)
    s = L.index(P_s)
    
    ch = [0] * n
    x = [0] * n
    z = [0] * n
    
    ch[(s + 1) % n] = hash_func(PP.q, m, L, I_scope, SID, C_1, C_2, L_s, R_s, A_s, B_s)
    
    for j in range(1, n):
        i = (s + j) % n
        x[i] = random.randint(1, PP.q - 1)
        z[i] = random.randint(1, PP.q - 1)
        
        P_i = L[i]
        H_p_i = hash_to_point(P_i, SID, PP.curve, PP.p, PP.a, PP.b)
        
        L_i = (x[i] * PP.G) + (ch[i] * P_i)
        R_i = (x[i] * H_p_i) + (ch[i] * I_scope)
        
        A_i = sub_points(z[i] * PP.G, ch[i] * C_1, PP.q)
        C2_minus_Pi = sub_points(C_2, P_i, PP.q)
        B_i = sub_points(z[i] * PP.P_net, ch[i] * C2_minus_Pi, PP.q)
        
        ch[(i + 1) % n] = hash_func(PP.q, m, L, I_scope, SID, C_1, C_2, L_i, R_i, A_i, B_i)
        
    x[s] = (r - (ch[s] * S_s)) % PP.q
    z[s] = (r_z + (ch[s] * r_dean)) % PP.q
    
    sigma = (I_scope, L, SID, PP.P_net, C_1, C_2, ch[0], x, z)
    return sigma

# --- Algorithm 2: Verify  ---
def verify(m, sigma, PP):
    if not sigma:
        return 0
        
    I_scope, L, SID, P_net, C_1, C_2, ch_0, x, z = sigma
    
    if (L not in PP.L_registry) or (SID not in PP.SIDs) or (P_net != PP.P_net) or (len(L) < PP.n_min):
        return 0
        
    n = len(L)
    ch = [0] * n
    ch[0] = ch_0
    
    P_0 = L[0]
    H_p_0 = hash_to_point(P_0, SID, PP.curve, PP.p, PP.a, PP.b)
    
    L_1_prime = (x[0] * PP.G) + (ch[0] * P_0)
    R_1_prime = (x[0] * H_p_0) + (ch[0] * I_scope)
    
    A_1_prime = sub_points(z[0] * PP.G, ch[0] * C_1, PP.q)
    C2_minus_P0 = sub_points(C_2, P_0, PP.q)
    B_1_prime = sub_points(z[0] * P_net, ch[0] * C2_minus_P0, PP.q)
    
    ch[1 % n] = hash_func(PP.q, m, L, I_scope, SID, C_1, C_2, L_1_prime, R_1_prime, A_1_prime, B_1_prime)
    
    for i in range(1, n):
        P_i = L[i]
        H_p_i = hash_to_point(P_i, SID, PP.curve, PP.p, PP.a, PP.b)
        
        L_i_prime = (x[i] * PP.G) + (ch[i] * P_i)
        R_i_prime = (x[i] * H_p_i) + (ch[i] * I_scope)
        
        A_i_prime = sub_points(z[i] * PP.G, ch[i] * C_1, PP.q)
        C2_minus_Pi = sub_points(C_2, P_i, PP.q)
        B_i_prime = sub_points(z[i] * P_net, ch[i] * C2_minus_Pi, PP.q)
        
        computed_ch = hash_func(PP.q, m, L, I_scope, SID, C_1, C_2, L_i_prime, R_i_prime, A_i_prime, B_i_prime)
        
        next_i = (i + 1) % n
        if next_i == 0:
            if computed_ch == ch[0]:
                return 1
        else:
            ch[next_i] = computed_ch
            
    return 0

# --- Algorithm 3: Link  ---
def link(sigma_1, m_1, sigma_2, m_2, PP):
    if not sigma_1 or not sigma_2:
        return 0
        
    SID_1 = sigma_1[2]
    SID_2 = sigma_2[2]
    
    if SID_1 != SID_2:
        return 0
        
    if (verify(m_1, sigma_1, PP) == 1) and (verify(m_2, sigma_2, PP) == 1):
        if sigma_1[0] == sigma_2[0]:
            return 1
            
    return 0

# --- Algorithm 4: Deanonymize  ---
def deanonymize(sigma, D_list, omega_list, q):
    C_1 = sigma[4]
    C_2 = sigma[5]
    k = len(D_list)
    
    lam = [0] * k
    
    for j in range(k):
        num = 1
        den = 1
        for i in range(k):
            if i != j:
                num = (num * omega_list[i]) % q
                diff = (omega_list[i] - omega_list[j]) % q
                den = (den * diff) % q
                
        #verif this part
        den_inv = pow(den, -1, q)
        lam[j] = (num * den_inv) % q
        
    V = INFINITY
    for j in range(k):
        term = lam[j] * D_list[j]
        if V == INFINITY:
            V = term
        else:
            V = V + term
            
    P_s = sub_points(C_2, V, q)
    return P_s

# Display function
def display_pp(PP):
    def format_item(item):
        if hasattr(item, 'x') and hasattr(item, 'y'):
            # Ec points P(x,y)
            x_val = item.x() if callable(item.x) else item.x
            y_val = item.y() if callable(item.y) else item.y
            return f"({x_val}, {y_val})"
        elif isinstance(item, list):
            return "[" + ", ".join(format_item(sub_item) for sub_item in item) + "]"
        elif isinstance(item, tuple):
            return "(" + ", ".join(format_item(sub_item) for sub_item in item) + ")"
        else:
            return str(item)

    for key, value in vars(PP).items():
        print(f"{key}: {format_item(value)}")

# size and time
def get_signature_size_bytes(n):
    return 97 * n + 196


if __name__ == "__main__":
    PP = SystemParameters()
        # Deanonymization Setup
    #network of N nodes where the threshold is k=8 (2/3)
    N = 12
    k = 8
    # Generate N shares
    all_shares = generate_shares(PP.S_net, N, k, PP.q)
    # How many public keys in global registry? K
    K = 32
    S_keys = []
    P_keys = []
    
    for _ in range(K):
        s = random.randint(1, PP.q - 1)
        S_keys.append(s)
        P_keys.append(s * PP.G)
    # Here the ring size is the registry size n = K, can be changed to sample n-1 random keys from K and later append signer public key    
    L = P_keys
    PP.L_registry.append(L)
    print("Secret keys are: ",S_keys)

    s_index = 1


    signer_S = S_keys[s_index]
    m_1 = "Consent_proof_V1"
    m_2 = "Consent_proof_V2"
    m_3 = "Consent_proof_V3"
    
    SID_A = PP.SIDs[0]
    SID_B = PP.SIDs[1]
    display_pp(PP)

    #SIGN
    start_time = time.perf_counter()
    sigma_1 = sign(m_1, signer_S, L, SID_A, PP)
    sign_time_1 = time.perf_counter() - start_time
    print(f"Sign Operation Time: {sign_time_1:.4f} seconds")
    sig_size = get_signature_size_bytes(len(L))
    print(f"Signature Size: {sig_size} bytes")
    sigma_2 = sign(m_2, signer_S, L, SID_A, PP)
    sigma_3 = sign(m_3, signer_S, L, SID_B, PP)
    
    # VERIFY
    start_time = time.perf_counter()
    v1_result = verify(m_1, sigma_1, PP)
    verify_time_1 = time.perf_counter() - start_time
    print(f"Verification of Sigma 1: {'Pass' if v1_result == 1 else 'Fail'}(Time: {verify_time_1:.4f} seconds)")
    print(f"Verification of Sigma 2: {'Pass' if verify(m_2, sigma_2, PP) == 1 else 'Fail'}")
    print(f"Verification of Sigma 3: {'Pass' if verify(m_3, sigma_3, PP) == 1 else 'Fail'}")

    # LINK
    start_time = time.perf_counter()
    link_1_2 = link(sigma_1, m_1, sigma_2, m_2, PP)
    link_time_1_2 = time.perf_counter() - start_time
    print(f"Link(Sigma 1, Sigma 2) [Same SID]: {link_1_2} (Time: {link_time_1_2:.4f} seconds)")
    link_1_3 = link(sigma_1, m_1, sigma_3, m_3, PP)
    print(f"Link(Sigma 1, Sigma 3) [Diff SID]: {link_1_3}")

    # random k-of-N nodes respond to deanonymization request
    responding_nodes = random.sample(all_shares, k)

    omega_list = []
    D_list = []
    for node in responding_nodes:
        omega_j = node['omega']
        S_net_j = node['S_net_j']
        
        # Node computes its transient decryption share: D_j = S_{net-j} * C_1 // C_1 = Sigma[4]
        D_j = S_net_j * sigma_1[4] 
        
        omega_list.append(omega_j)
        D_list.append(D_j)

    # DEANONYMIZE
    start_time = time.perf_counter()
    Signer_PS = deanonymize(sigma_1, D_list, omega_list, PP.q)
    deanonymize_time = time.perf_counter() - start_time
    expected_P_s = P_keys[s_index]
    print(f"Deanonymization Operation Time: {deanonymize_time:.4f} seconds")
    print("extracted signer via dean is",point_to_str(Signer_PS))
    print("Designated signer was:",point_to_str(P_keys[s_index]))
    print("Correct deanonymization",P_keys[s_index] == Signer_PS)