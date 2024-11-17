import numpy

G0_BOX = [0, 1, 2, 0xb, 4, 5, 6, 0xf, 8, 9, 0xa, 3, 0xd, 0xc, 7, 0xe]
# self.G1_BOX = [0, 1, 2, 3, 4, 7, 6, 5, 8, 9, 0xe, 0xd, 0xc, 0xf, 0xa, 0xb]
G1_BOX = [0, 2, 4, 6, 8, 0xe, 0xc, 0xa, 1, 3, 7, 5, 9, 0xd, 0xf, 0xb]


def create_ddt(g_box):
    ddt = numpy.zeros((16, 16), dtype=numpy.int32)
    for i in range(16):
        for diff in range(16):
            n_i = i ^ diff
            i_out = g_box[i]
            n_i_out = g_box[n_i]
            ddt[diff][i_out ^ n_i_out] += 1
    return ddt


def create_bct():
    bct = numpy.zeros((16, 16), dtype=numpy.int32)
    for d_in in range(16):
        for d_out in range(16):
            for x in range(16):
                r1 = G1_BOX[x] ^ G0_BOX[x]
                r2 = G1_BOX[x ^ d_in] ^ G0_BOX[x ^ d_in]
                r3 = G1_BOX[x ^ d_out] ^ G0_BOX[x ^ d_out]
                r4 = G1_BOX[x ^ d_in ^ d_out] ^ G0_BOX[x ^ d_in ^ d_out]
                r = r1 ^ r2 ^ r3 ^ r4
                if r == 0:
                    bct[d_in][d_out] += 1
    return bct


d = create_bct()
numpy.savetxt("output.csv", d, delimiter=",", fmt="%d")
