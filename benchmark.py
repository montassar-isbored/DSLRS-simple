import hashlib
import random
import time
import csv
import statistics
import matplotlib.pyplot as plt
from ecdsa import SECP256k1
from ecdsa.ellipticcurve import Point, INFINITY

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

def point_to_str(pt):
    if pt == INFINITY:
        return "INFINITY"
    return f"{pt.x()},{pt.y()}"

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
    for j in range(1, N + 1):
        x = j
        y = 0
        for power, coeff in enumerate(coefficients):
            y = (y + coeff * pow(x, power, q)) % q
        shares.append({'omega': x, 'S_net_j': y})
    return shares

def sub_points(P1, P2, q):
    return P1 + ((q - 1) * P2)

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

if __name__ == "__main__":
    K_values = [8, 16, 32]
    runs_per_K = 100
    csv_filename = "protocol_benchmarks.csv"

    # Dictionary to hold averages for plotting
    avg_results = {"Sign": [], "Verify": [], "Link": [], "Deanonymize": []}

    print(f"Starting execution. Results will be saved to {csv_filename} and benchmark_plot.png")

    with open(csv_filename, mode='w', newline='') as csvfile:
        writer = csv.writer(csvfile)
        writer.writerow(["K", "Run", "Sign_Time_s", "Verify_Time_s", "Link_Time_s", "Deanonymize_Time_s"])

        for K in K_values:
            sign_latencies = []
            verify_latencies = []
            link_latencies = []
            deanonymize_latencies = []

            for run in range(1, runs_per_K + 1):
                PP = SystemParameters()
                N = 12
                k = 8
                all_shares = generate_shares(PP.S_net, N, k, PP.q)
                
                S_keys = []
                P_keys = []
                
                for _ in range(K):
                    s = random.randint(1, PP.q - 1)
                    S_keys.append(s)
                    P_keys.append(s * PP.G)
                    
                L = P_keys
                PP.L_registry.append(L)

                s_index = 1
                signer_S = S_keys[s_index]
                m_1 = "Consent_proof_V1"
                m_2 = "Consent_proof_V2"
                
                SID_A = PP.SIDs[0]

                # Measure Sign
                start_time = time.perf_counter()
                sigma_1 = sign(m_1, signer_S, L, SID_A, PP)
                sign_time = time.perf_counter() - start_time
                sign_latencies.append(sign_time)

                sigma_2 = sign(m_2, signer_S, L, SID_A, PP)
                
                # Measure Verify
                start_time = time.perf_counter()
                verify(m_1, sigma_1, PP)
                verify_time = time.perf_counter() - start_time
                verify_latencies.append(verify_time)

                # Measure Link
                start_time = time.perf_counter()
                link(sigma_1, m_1, sigma_2, m_2, PP)
                link_time = time.perf_counter() - start_time
                link_latencies.append(link_time)

                # Setup Deanonymize
                responding_nodes = random.sample(all_shares, k)
                omega_list = []
                D_list = []
                for node in responding_nodes:
                    D_j = node['S_net_j'] * sigma_1[4] 
                    omega_list.append(node['omega'])
                    D_list.append(D_j)

                # Measure Deanonymize
                start_time = time.perf_counter()
                deanonymize(sigma_1, D_list, omega_list, PP.q)
                deanonymize_time = time.perf_counter() - start_time
                deanonymize_latencies.append(deanonymize_time)

                writer.writerow([K, run, sign_time, verify_time, link_time, deanonymize_time])

            # Calculate and store averages
            avg_sign = statistics.mean(sign_latencies)
            avg_verify = statistics.mean(verify_latencies)
            avg_link = statistics.mean(link_latencies)
            avg_deanonymize = statistics.mean(deanonymize_latencies)
            
            avg_results["Sign"].append(avg_sign)
            avg_results["Verify"].append(avg_verify)
            avg_results["Link"].append(avg_link)
            avg_results["Deanonymize"].append(avg_deanonymize)

            print(f"--- K = {K} ---")
            print(f"Sign: {avg_sign:.4f}s, Verify: {avg_verify:.4f}s, Link: {avg_link:.4f}s, Dean: {avg_deanonymize:.4f}s")

    # Generate the bar plot
    x = range(len(K_values))
    width = 0.2

    fig, ax = plt.subplots(figsize=(10, 6))
    ax.bar([pos - 1.5 * width for pos in x], avg_results["Sign"], width, label='Sign')
    ax.bar([pos - 0.5 * width for pos in x], avg_results["Verify"], width, label='Verify')
    ax.bar([pos + 0.5 * width for pos in x], avg_results["Link"], width, label='Link')
    ax.bar([pos + 1.5 * width for pos in x], avg_results["Deanonymize"], width, label='Deanonymize')

    ax.set_ylabel('Average Latency (seconds)')
    ax.set_xlabel('Number of Keys in Global Registry (K)')
    ax.set_title('Average Cryptographic Operation Latency by K (100 runs each)')
    ax.set_xticks(x)
    ax.set_xticklabels(K_values)
    ax.legend()
    plt.grid(axis='y', linestyle='--', alpha=0.7)
    plt.tight_layout()
    
    plt.savefig('benchmark_plot.png')
    print("Plot successfully saved to benchmark_plot.png")