import numpy as np

PERM_64 = [7, 4, 1, 6, 3, 0, 5, 2]

PERM_128 = [14, 15, 8, 9, 2, 3, 12, 13, 6, 7, 0, 1, 10, 11, 4, 5]


# 0=0 1=1 2=?

def perm(perm_constant, bit_matrix):
    new_res = np.zeros(bit_matrix.shape, dtype=int)
    for i in range(4):
        for j in range(len(bit_matrix[0])):
            new_res[i][perm_constant[j]] = bit_matrix[i][j]
    return new_res


def cal_result(a, b, operator='^'):
    if operator == '&':
        return 2 if a + b > 0 else max(a, b)
    return a ^ b if a < 2 and b < 2 else max(a, b)


def left_rot_cycling(bit_matrix, num):
    new_res = np.zeros(bit_matrix.shape, dtype=int)
    bit_matrix[0][0] = 1
    for i in range(4):
        for j in range(len(bit_matrix[0])):
            new_res[i][j - num] = bit_matrix[i][j]
    return new_res


def g0(bit_matrix, col):
    new_res = np.zeros(bit_matrix.shape, dtype=int)
    for i in range(col):
        new_res[0][i] = cal_result(cal_result(bit_matrix[3][i], bit_matrix[2][i], '&'), bit_matrix[0][i])
        new_res[3][i] = cal_result(cal_result(new_res[0][i], bit_matrix[1][i], '&'), bit_matrix[3][i])
        new_res[2][i] = bit_matrix[2][i]
        new_res[1][i] = bit_matrix[1][i]
    return new_res


def g1(bit_matrix, col):
    roted_bit_matrix = left_rot_cycling(bit_matrix, 1)
    new_res = np.zeros(bit_matrix.shape, dtype=int)
    for i in range(col):
        new_res[0][i] = roted_bit_matrix[0][i]
        new_res[3][i] = roted_bit_matrix[3][i]
        new_res[2][i] = cal_result(cal_result(roted_bit_matrix[3][i], roted_bit_matrix[1][i], '&'),
                                   roted_bit_matrix[2][i])
        new_res[1][i] = cal_result(cal_result(new_res[2][i], roted_bit_matrix[0][i], '&'), roted_bit_matrix[1][i])
    return new_res


def wrap_data(bits_str):
    size = len(bits_str)
    wrap_matrix = np.zeros((4, size // 4), dtype=int)
    start_index = size - 1
    for i in range(size // 4):
        for j in range(3, -1, -1):
            wrap_matrix[j][i] = bits_str[start_index]
            start_index -= 1
    return wrap_matrix


def xor_op(a, b):
    new_res = np.zeros(a.shape, dtype=int)
    for i in range(4):
        for j in range(len(a[0])):
            new_res[i][j] = max(a[i][j], b[i][j])
    return new_res


def format_print(matrix):
    col_num = len(matrix[0])
    row_num = len(matrix)
    new_result = np.zeros(col_num * row_num, dtype=str)
    start_index = 0
    for i in range(col_num):
        for j in range(row_num - 1, -1, -1):
            value = matrix[j][i]
            new_result[start_index] = str(value) if value < 2 else '?'
            start_index += 1
    new_result = ''.join(new_result)
    return new_result


def search_characteristic(left, right, size):
    left_binary = format(left, 'b').zfill(size)
    right_binary = format(right, 'b').zfill(size)

    left_binary = wrap_data(left_binary)
    right_binary = wrap_data(right_binary)

    perm_cons = PERM_64 if size == 32 else PERM_128

    g0_out = g0(left_binary, size // 4)
    g1_out = g1(left_binary, size // 4)
    g01_out = xor_op(g0_out, g1_out)
    perm_out = perm(perm_cons, g01_out)
    final_res = xor_op(perm_out, right_binary)
    print(format_print(final_res))
    return final_res


search_characteristic(0x00100908, 0x00021012, 32)
