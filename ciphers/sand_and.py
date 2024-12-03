from tokenize import group

from ciphers.cipher import AbstractCipher
from parser import stpcommands
import util
import itertools
import numpy as np


def switch_searching(param, word_size):
    if len(param['previous_trail']) <= 0:
        return ""
    previous_trails = param['previous_trail']
    data = param['previous_trail'][-1]
    trails_data = data.getData()

    r = param['rounds']

    param["blockedCharacteristics"].clear()
    param["fixedVariables"].clear()

    # input diff
    input_diff_l = trails_data[0][0]
    input_diff_r = trails_data[0][1]
    param["fixedVariables"]["XL0"] = input_diff_l
    param["fixedVariables"]["XR0"] = input_diff_r

    # output diff
    output_diff_l = trails_data[r][2]
    output_diff_r = trails_data[r][3]
    param["fixedVariables"]["YL{}".format(r)] = output_diff_l
    param["fixedVariables"]["YR{}".format(r)] = output_diff_r

    command = ""
    start_rounds = param["em_start_search_num"]
    end_round = param['em_end_search_num']
    if len(previous_trails) > 0:
        command = "ASSERT(NOT("
        for characteristic in previous_trails:
            trails_data = characteristic.getData()
            str1 = "(BVXOR(XL{0},{1})|BVXOR(YR{2}, {3}))".format(
                start_rounds, trails_data[start_rounds][0], end_round,
                trails_data[end_round][3])

            command += str1
            command += "&"
        command = command[:-1]
        command += "=0x{}));\n".format('0' * (word_size // 4))
    return command


class Sand(AbstractCipher):
    name = 'sand'

    alpha = 0

    beta = 1

    def __init__(self):
        self.PERM = None

    def createSTP(self, filename, parameters):
        word_size = parameters["wordsize"]
        rounds = parameters["rounds"]
        weight = parameters["sweight"]
        switch_start_round = parameters["switchStartRound"]
        switch_rounds = parameters["switchRounds"]
        block_size = word_size // 2

        e0_start_search_num = 0
        e0_end_search_num = rounds if switch_start_round == -1 else switch_start_round
        em_start_search_num = rounds if switch_start_round == -1 else switch_start_round
        em_end_search_num = (
            rounds if switch_start_round == -1 else em_start_search_num + switch_rounds
        )
        e1_start_search_num = (
            rounds if switch_start_round == -1 else switch_start_round + switch_rounds
        )
        e1_end_search_num = rounds

        parameters["em_start_search_num"] = em_start_search_num
        parameters["em_end_search_num"] = em_end_search_num

        if block_size == 32:
            self.PERM = [7, 4, 1, 6, 3, 0, 5, 2]
        elif block_size == 64:
            self.PERM = [14, 15, 8, 9, 2, 3, 12, 13, 6, 7, 0, 1, 10, 11, 4, 5]

        with open(filename, 'w') as stp_file:
            header = ("% Input File for STP\n% Sand{} w={} Rounds={}\n\n\n".format(word_size, weight,
                                                                                   rounds))
            stp_file.write(header)
            command = ""
            variables = initial_file(rounds, block_size, weight, stp_file)

            # loading init diff
            # self.pre_round(stp_file, xl[0], xr[0], xl[1], xr[1], block_size)

            for i in range(e0_start_search_num, e0_end_search_num):
                self.setup_round(stp_file, variables["xl"][i], variables["xr"][i],
                                 variables["xl"][i + 1], variables["xr"][i + 1],
                                 variables["g0_rot"][i], variables["g0_and"][i], variables["g0_box_out"][i],
                                 variables["g1_rot"][i], variables["g1_and"][i], variables["g1_box_out"][i],
                                 variables["g01_xor_out"][i], variables["perm_out"][i], variables["w"][i], block_size)
            # BCT
            for i in range(em_start_search_num, em_end_search_num):
                and_bct(stp_file, variables["xl"][i], variables["yr"][i + 1], block_size)

            for i in range(e1_start_search_num, e1_end_search_num):
                self.setup_round(stp_file, variables["yl"][i], variables["yr"][i],
                                 variables["yl"][i + 1], variables["yr"][i + 1],
                                 variables["g0_rot"][i], variables["g0_and"][i], variables["g0_box_out"][i],
                                 variables["g1_rot"][i], variables["g1_and"][i], variables["g1_box_out"][i],
                                 variables["g01_xor_out"][i], variables["perm_out"][i], variables["w"][i], block_size)

            # searching for simple trails
            if not parameters['cluster'] and not parameters["search_switches"]:
                command += self.pre_handle(parameters, block_size)
            # searching for switches with fixed input and output differ
            if parameters["search_switches"] == 1:
                command += switch_searching(parameters, block_size)

            stp_file.write(command)
            stpcommands.assertNonZero(stp_file, [variables["xl"][0]], block_size)
            if switch_rounds > 0:
                stpcommands.assertNonZero(stp_file, [variables["yl"][rounds], variables["yr"][rounds]],
                                          block_size)

            for key, value in parameters["fixedVariables"].items():
                stpcommands.assertVariableValue(stp_file, key, value)
            stpcommands.setupQuery(stp_file)

    def pre_round(self, stp_file, in_left, in_right, out_left, out_right, block_size):
        re_sharp = util.sand_t(block_size)
        command = ""
        for i in range(block_size):
            command += "ASSERT({0}[{1}:{1}]={2}[{3}:{3}]);\n".format(out_left, i, in_left, re_sharp[i])
            command += "ASSERT({0}[{1}:{1}]={2}[{3}:{3}]);\n".format(out_right, i, in_right, re_sharp[i])
        stp_file.write(command)

    def setup_round(self, stp_file, in_left, in_right, out_left, out_right,
                    g0_rot, g0_and, g0_box_out,
                    g1_rot, g1_and, g1_box_out,
                    g01_xor_out, perm_out, w, block_size, switch=False):

        command = "\n\nASSERT({} = {});\n".format(out_right, in_left)

        group_size = block_size // 4

        # G_0
        command += "\n\n% Compute G0\n"
        g0_rot_index = util.sand_rot(block_size, self.alpha)

        if self.alpha != 0:
            for i in range(block_size):
                command += "ASSERT({0}[{1}:{1}]={2}[{3}:{3}]);".format(g0_rot, i, in_left, g0_rot_index[i])
        else:
            command += "ASSERT({0}={1});".format(g0_rot, in_left)

        command += "\n"
        # a0=x3*x2+x0
        command += "ASSERT({0}[{1}:{2}]={3}[{4}:{5}]|{3}[{6}:{7}]);\n".format(g0_and,
                                                                              group_size * 1 - 1, group_size * 0,
                                                                              g0_rot,
                                                                              group_size * 1 - 1, group_size * 0,
                                                                              group_size * 2 - 1, group_size * 1)

        command += "ASSERT(BVLE({0}[{1}:{2}],{0}[{3}:{4}]));\n".format(g0_and,
                                                                       group_size * 2 - 1, group_size * 1,
                                                                       group_size * 1 - 1, group_size * 0)

        command += "ASSERT({0}[{1}:{2}]=BVXOR({3}[{4}:{5}],{6}[{7}:{8}]));\n".format(g0_box_out,
                                                                                     group_size * 1 - 1, group_size * 0,
                                                                                     g0_and,
                                                                                     group_size * 2 - 1, group_size * 1,
                                                                                     g0_rot,
                                                                                     group_size * 1 - 1, group_size * 0,
                                                                                     )

        # a3=a0*x1+x3
        command += "ASSERT({0}[{1}:{2}]={3}[{4}:{5}]|{6}[{7}:{8}]);\n".format(g0_and,
                                                                              group_size * 3 - 1, group_size * 2,
                                                                              g0_box_out,
                                                                              group_size * 1 - 1, group_size * 0,
                                                                              g0_rot,
                                                                              group_size * 2 - 1, group_size * 1)

        command += "ASSERT(BVLE({0}[{1}:{2}],{0}[{3}:{4}]));\n".format(g0_and,
                                                                       group_size * 4 - 1, group_size * 3,
                                                                       group_size * 3 - 1, group_size * 2)

        command += "ASSERT({0}[{1}:{2}]=BVXOR({3}[{4}:{5}],{6}[{7}:{8}]));\n".format(g0_box_out,
                                                                                     group_size * 1 - 1, group_size * 0,
                                                                                     g0_and,
                                                                                     group_size * 4 - 1, group_size * 3,
                                                                                     g0_rot,
                                                                                     group_size * 4 - 1, group_size * 3,
                                                                                     )
        # a2 = x2
        command += "ASSERT({0}[{2}:{3}]={1}[{2}:{3}]);\n".format(g0_box_out, g0_rot,
                                                                 group_size * 3 - 1, group_size * 2
                                                                 )
        # a1 = x1
        command += "ASSERT({0}[{2}:{3}]={1}[{2}:{3}]);\n".format(g0_box_out, g0_rot,
                                                                 group_size * 2 - 1, group_size * 1
                                                                 )

        # G_1
        command += "\n\n% Compute G1\n"
        g1_rot_index = util.sand_rot(block_size, self.beta)

        if self.beta != 0:
            for i in range(block_size):
                command += "ASSERT({0}[{1}:{1}]={2}[{3}:{3}]);".format(g1_rot, i, in_left, g1_rot_index[i])
        else:
            command += "ASSERT({0}={1});".format(g1_rot, in_left)

        # b2 = x3 * x1 + x2
        command += "ASSERT({0}[{1}:{2}]={3}[{4}:{5}]|{3}[{6}:{7}]);\n".format(g1_and,
                                                                              group_size * 1 - 1, group_size * 0,
                                                                              g0_rot,
                                                                              group_size * 4 - 1, group_size * 3,
                                                                              group_size * 2 - 1, group_size * 1)

        command += "ASSERT(BVLE({0}[{1}:{2}],{0}[{3}:{4}]));\n".format(g1_and,
                                                                       group_size * 2 - 1, group_size * 1,
                                                                       group_size * 1 - 1, group_size * 0)

        command += "ASSERT({0}[{1}:{2}]=BVXOR({3}[{4}:{5}],{6}[{7}:{8}]));\n".format(g1_box_out,
                                                                                     group_size * 3 - 1, group_size * 2,
                                                                                     g1_and,
                                                                                     group_size * 2 - 1, group_size * 1,
                                                                                     g1_rot,
                                                                                     group_size * 3 - 1, group_size * 2,
                                                                                     )
        # b1=b2*x0+x1
        command += "ASSERT({0}[{1}:{2}]={3}[{4}:{5}]|{6}[{7}:{8}]);\n".format(g1_and,
                                                                              group_size * 3 - 1, group_size * 2,
                                                                              g1_box_out,
                                                                              group_size * 3 - 1, group_size * 2,
                                                                              g1_rot,
                                                                              group_size * 1 - 1, group_size * 0)

        command += "ASSERT(BVLE({0}[{1}:{2}],{0}[{3}:{4}]));\n".format(g1_and,
                                                                       group_size * 4 - 1, group_size * 3,
                                                                       group_size * 3 - 1, group_size * 2)

        command += "ASSERT({0}[{1}:{2}]=BVXOR({3}[{4}:{5}],{6}[{7}:{8}]));\n".format(g1_box_out,
                                                                                     group_size * 2 - 1, group_size * 1,
                                                                                     g1_and,
                                                                                     group_size * 4 - 1, group_size * 3,
                                                                                     g1_rot,
                                                                                     group_size * 2 - 1, group_size * 1,
                                                                                     )
        # b3 = x3
        command += "ASSERT({0}[{2}:{3}]={1}[{2}:{3}]);\n".format(g1_box_out, g1_rot,
                                                                 group_size * 4 - 1, group_size * 3
                                                                 )
        # b0 = x0
        command += "ASSERT({0}[{2}:{3}]={1}[{2}:{3}]);\n".format(g1_box_out, g1_rot,
                                                                 group_size * 1 - 1, group_size * 0
                                                                 )

        command += "\n\n % Compute XOR(G0,G1)\n"
        # G1 xor G2
        command += "ASSERT({0} = BVXOR({1},{2}));\n".format(g01_xor_out, g0_box_out, g1_box_out)
        command += "\n\n % Compute PERM(XOR(G0,G1))\n"
        # P_out
        for i in range(4):
            for j, k in enumerate(self.PERM):
                command += "ASSERT({0}[{1}:{1}] = {2}[{3}:{3}]);".format(perm_out, i * group_size + k,
                                                                         g01_xor_out, i * group_size + j)

        command += ("\nASSERT({0} = BVXOR({1},{2}));\n".format(out_left, in_right, perm_out))

        command += "\n\n % Compute WEIGHT\n"
        # compute weight

        command += "ASSERT({0}={1}@{2});\n".format(w, g0_and, g1_and)

        stp_file.write(command)

    def get_cluster_params(self, parameters, prob, total_prob):
        pass

    def create_cluster_parameters(self, new_parameters, characteristic):
        # Cluster Search Setting
        trails_data = characteristic.getData()

        r = new_parameters['rounds']
        start_rounds = new_parameters["em_start_search_num"]
        switch_round = new_parameters['em_end_search_num']

        new_parameters["blockedCharacteristics"].clear()
        new_parameters["fixedVariables"].clear()

        # fixed input
        input_diff_l = trails_data[0][0]
        input_diff_r = trails_data[0][1]
        new_parameters["fixedVariables"]["XL0"] = input_diff_l
        new_parameters["fixedVariables"]["XR0"] = input_diff_r

        # fixed output
        output_diff_l = trails_data[r][2]
        output_diff_r = trails_data[r][3]
        new_parameters["fixedVariables"]["YL{}".format(r)] = output_diff_l
        new_parameters["fixedVariables"]["YR{}".format(r)] = output_diff_r

        # fix boomerang switch
        switch_in = trails_data[start_rounds][0]
        switch_out = trails_data[switch_round][3]
        new_parameters["fixedVariables"]["XL{}".format(start_rounds)] = switch_in
        new_parameters["fixedVariables"]["YR{}".format(switch_round)] = switch_out

    def get_diff_hex(self, parameters, characteristics):
        switch_start_round = parameters['switchStartRound']
        switch_rounds = parameters['switchRounds']
        r = parameters['rounds']
        trails_data = characteristics.getData()
        # input diff
        input_diff_l = trails_data[0][0]
        input_diff_r = trails_data[0][1]
        input_diff = input_diff_l + input_diff_r.replace("0x", "")

        # output diff
        output_diff_l = trails_data[r][2]
        output_diff_r = trails_data[r][3]
        output_diff = output_diff_l + output_diff_r.replace("0x", "")

        # switch diff
        switch_input_diff_l = trails_data[switch_start_round][0]
        switch_input_diff_r = trails_data[switch_start_round][1]
        switch_output_diff_l = trails_data[switch_start_round + switch_rounds][2]
        switch_output_diff_r = trails_data[switch_start_round + switch_rounds][3]
        switch_input = switch_input_diff_l + switch_input_diff_r.replace("0x", "")
        switch_output = switch_output_diff_l + switch_output_diff_r.replace("0x", "")

        # switch weight
        switch_weight = trails_data[switch_start_round][10]

        return input_diff, switch_input, switch_output, output_diff, switch_weight

    def pre_handle(self, param, block_size):
        if 'countered_trails' not in param:
            return ""
        characters = param["countered_trails"]
        word_size = param['wordsize']
        command = ""
        if len(characters) > 0:
            r = param['rounds']
            command = "ASSERT(NOT("
            for characteristic in characters:
                trails_data = characteristic.getData()
                # input diff
                input_diff_l = trails_data[0][0]
                input_diff_r = trails_data[0][1]

                switch_rounds = param["switchRounds"]
                if switch_rounds < 0:
                    output_diff_l = trails_data[r][0]
                    output_diff_r = trails_data[r][1]
                    str1 = "(BVXOR(XL0,{0})|BVXOR(XR0, {1}) | BVXOR(XL{2}, {3}) | BVXOR(XR{2}, {4}))".format(
                        input_diff_l,
                        input_diff_r,
                        r,
                        output_diff_l,
                        output_diff_r)
                else:
                    # output diff
                    output_diff_l = trails_data[r][2]
                    output_diff_r = trails_data[r][3]
                    str1 = "(BVXOR(XL0,{0})|BVXOR(XR0, {1}) | BVXOR(YL{2}, {3}) | BVXOR(YR{2}, {4}))".format(
                        input_diff_l,
                        input_diff_r,
                        r,
                        output_diff_l,
                        output_diff_r)

                command += str1
                command += "&"
            command = command[:-1]
            command += "=0x{}));\n".format('0' * (block_size // 4))
            # switch

        return command

    def getFormatString(self):
        return ['XL', 'XR', 'YL', 'YR', 'AROT', 'AAND', 'ABOXOUT', 'BROT', 'BAND', 'BBOXOUT', 'ABXOROUT', 'POUT', 'w']


def initial_file(rounds, block_size, weight, stp_file):
    xl = ["XL{}".format(i) for i in range(rounds + 1)]
    xr = ["XR{}".format(i) for i in range(rounds + 1)]
    yl = ["YL{}".format(i) for i in range(rounds + 1)]
    yr = ["YR{}".format(i) for i in range(rounds + 1)]
    g0_rot = ["AROT{}".format(i) for i in range(rounds)]
    g0_and = ["AAND{}".format(i) for i in range(rounds)]
    g0_box_out = ["ABOXOUT{}".format(i) for i in range(rounds)]
    g1_rot = ["BROT{}".format(i) for i in range(rounds)]
    g1_and = ["BAND{}".format(i) for i in range(rounds)]
    g1_box_out = ["BBOXOUT{}".format(i) for i in range(rounds)]
    g01_xor_out = ["ABXOROUT{}".format(i) for i in range(rounds)]
    perm_out = ["POUT{}".format(i) for i in range(rounds)]
    w = ["w{}".format(i) for i in range(rounds)]

    stpcommands.setupVariables(stp_file, xl, block_size)
    stpcommands.setupVariables(stp_file, xr, block_size)
    stpcommands.setupVariables(stp_file, yl, block_size)
    stpcommands.setupVariables(stp_file, yr, block_size)
    stpcommands.setupVariables(stp_file, g0_rot, block_size)
    stpcommands.setupVariables(stp_file, g0_and, block_size)
    stpcommands.setupVariables(stp_file, g0_box_out, block_size)
    stpcommands.setupVariables(stp_file, g1_rot, block_size)
    stpcommands.setupVariables(stp_file, g1_and, block_size)
    stpcommands.setupVariables(stp_file, g1_box_out, block_size)
    stpcommands.setupVariables(stp_file, g01_xor_out, block_size)
    stpcommands.setupVariables(stp_file, perm_out, block_size)
    stpcommands.setupVariables(stp_file, w, block_size * 2)
    stpcommands.setupWeightComputation(stp_file, weight, w, block_size * 2)
    # setupWeightComputationSum(stp_file, weight, w, block_size)
    return {"xl": xl, "xr": xr, "yl": yl, "yr": yr, "g0_rot": g0_rot, "g0_box_out": g0_box_out,
            "g1_rot": g1_rot, "g1_box_out": g1_box_out, "perm_out": perm_out, "w": w, "g01_xor_out": g01_xor_out,
            "g0_and": g0_and, "g1_and": g1_and}


def setupWeightComputationSum(stpfile, weight, p, wordsize, ignoreMSBs=0):
    """
    Assert that weight is equal to the sum of p.
    """
    stpfile.write("weight: BITVECTOR(16);\n")
    round_sum = ""
    for w in p:
        round_sum += w + ","
    if len(p) > 1:
        stpfile.write("ASSERT(weight = BVPLUS({},{}));\n".format(16, round_sum[:-1]))
    else:
        stpfile.write("ASSERT(weight = {});\n".format(round_sum[:-1]))

    stpfile.write("ASSERT(weight = {0:#018b});\n".format(weight))
    return


def and_bct(stp_file, a, b, block_size):
    command = ""
    group_size = block_size // 4
    str_template = "ASSERT(BVXOR({0}[{2}:{3}]&{1}[{4}:{5}], {0}[{4}:{5}]&{1}[{2}:{3}])=0bin0);\n"

    # G_0
    command += str_template.format(a, b,
                                   group_size * 1 - 1, group_size * 0,
                                   group_size * 2 - 1, group_size * 1
                                   )
    command += str_template.format(a, b,
                                   group_size * 2 - 1, group_size * 1,
                                   group_size * 3 - 1, group_size * 2
                                   )
    command += str_template.format(a, b,
                                   group_size * 2 - 1, group_size * 1,
                                   group_size * 4 - 1, group_size * 3
                                   )
    command += str_template.format(a, b,
                                   group_size * 3 - 1, group_size * 2,
                                   group_size * 4 - 1, group_size * 3
                                   )

    # G_1
    command += str_template.format(a, b,
                                   group_size * 1 - 1, group_size * 0,
                                   group_size * 3 - 1, group_size * 2
                                   )
    command += str_template.format(a, b,
                                   group_size * 1 - 1, group_size * 0,
                                   group_size * 4 - 1, group_size * 3
                                   )
    command += str_template.format(a, b,
                                   group_size * 3 - 1, group_size * 2,
                                   group_size * 4 - 1, group_size * 3
                                   )
    command += str_template.format(a, b,
                                   group_size * 2 - 1, group_size * 1,
                                   group_size * 3 - 1, group_size * 2
                                   )
    stp_file.write(command)
