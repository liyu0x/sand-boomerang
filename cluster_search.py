from argparse import ArgumentParser, RawTextHelpFormatter
import yaml
from ciphers import sand_sbox
import time
import util
import random
from cryptanalysis import search
import copy
import math
import uuid
from config import (USE_SHARP)
import re

CIPHER_MAPPING = {"sand": sand_sbox.Sand()}

TEMP_DIC = "tmp/"

STORE = []

TOTAL_PROB = 0


def checkout_results(params, file):
    if len(params["previous_trail"]) == 0:
        return
    data = params["previous_trail"][-1]
    trails_data = data.getData()
    r = params['rounds']
    start_rounds = params["em_start_search_num"]
    switch_round = params['em_end_search_num']

    # input differ
    input_diff_l = trails_data[0][0]
    input_diff_r = trails_data[0][1]

    # output differ
    output_diff_l = trails_data[r][2]
    output_diff_r = trails_data[r][3]

    log = ("Rounds: {}, probability: {}, Input Left:{}, Input Right:{}, Output Left:{}, Output Right:{}\n"
           .format(r,
                   math.log2(
                       TOTAL_PROB),
                   input_diff_l,
                   input_diff_r,
                   output_diff_l,
                   output_diff_r))

    file.write(log)

    for trail in params["previous_trail"]:
        trails_data = trail.getData()
        switch_in = trails_data[start_rounds][0]
        switch_out = trails_data[switch_round][3]
        weight = trail.weight
        switch_weight = trails_data[start_rounds][10]
        log = "\t\t switch in:{}, switch out:{}, trail weight:{}, switch weight:{}\n".format(switch_in, switch_out,
                                                                                             weight, switch_weight)

        file.write(log)

    file.flush()


def check_solutions(new_parameter, cipher, threshold, cluster_count):
    sol_counter = 0
    start_time = str(uuid.uuid4())
    stp_file = TEMP_DIC + "{}{}-{}.stp".format(cipher.name, "clutesr", start_time)
    count = 1
    cluster_counter = 0
    solutions_map = {}
    while count < threshold and cluster_counter < cluster_count:
        cluster_counter += 1
        cipher.createSTP(stp_file, new_parameter)

        # Start solver
        sat_process = search.startSATsolver(stp_file)

        # Find the number of solutions with the SAT solver
        print("Finding all trails of weight {}\n".format(new_parameter["sweight"]))

        # Watch the process and count solutions
        solutions = 0
        while sat_process.poll() is None:
            lines = sat_process.stdout.readlines()
            if USE_SHARP == 1:
                done = False
                for line in lines:
                    if "exact arb" in line.decode("utf-8"):
                        done = True
                if not done:
                    continue
                line = lines[len(lines) - 1].decode("utf-8")
                pattern = re.compile('\d+')
                solutions += int(pattern.search(line).group())
            else:
                for line in lines:
                    if "s SATISFIABLE" in line.decode("utf-8"):
                        solutions += 1
        if solutions > 0:
            solutions /= 2
            print("\tSolutions: {}".format(solutions))
            sol_counter += solutions

        solutions_map[new_parameter['sweight']] = solutions
        new_parameter['sweight'] += 1
        if solutions == 0:
            count += 1
        else:
            count = 0

    return sol_counter, solutions_map


def find_single_trail(cipher, r, lunch_arg):
    global TOTAL_PROB
    start_searching = False
    flag = lunch_arg['switchStartRound']
    task_start_time = time.time()
    valid_count = 0
    params = copy.deepcopy(lunch_arg)
    each_round_max_valid = int(lunch_arg['eachRoundMaxValid'])
    each_round_max_time = int(lunch_arg['eachRoundMaxTime']) * 3600
    rnd_string_tmp = "%030x" % random.randrange(16 ** 30)
    stp_file = TEMP_DIC + "{0}-{1}-{2}.stp".format(cipher.name, rnd_string_tmp, r)
    switch_timer = 0
    save_file = "results/" + "{0}-{1}.txt".format(cipher.name, lunch_arg["rounds"])
    result_file = open(save_file, "w+")
    report_flag = False
    while valid_count < each_round_max_valid and time.time() - task_start_time < each_round_max_time:
        params["cluster"] = False
        if switch_timer > 10:
            print("-----------------------------Switches searching end--------------------------------")
            checkout_results(params, result_file)
            params["sweight"] = lunch_arg["sweight"]
            params["countered_trails"].append(params["previous_trail"][0])
            params["previous_trail"].clear()
            valid_count += 1
            TOTAL_PROB = 0
            switch_timer = 0
            start_searching = False
            params["search_switches"] = False
            params["fixedVariables"].clear()

        params["cluster"] = 0
        if params['sweight'] >= lunch_arg['endweight']:
            break

        cipher.createSTP(stp_file, params)
        if params["boolector"]:
            result = search.solveBoolector(stp_file)
        else:
            result = search.solveSTP(stp_file)
        if not search.foundSolution(result):
            print(
                "Rounds:{1}, No trails, weight:{0}\n".format(
                    params["sweight"], params["rounds"]
                )
            )
            params["sweight"] += 1
            if start_searching:
                switch_timer += 1
            continue

        characteristic = search.parsesolveroutput.getCharSTPOutput(result, cipher, params["rounds"])
        characteristic.printText()
        params['previous_trail'].append(characteristic)
        params["search_switches"] = True
        if params["search_switches"] and switch_timer == 0:
            print("-----------------------------Switches searching start--------------------------------")
        start_searching = True
        if flag != -1:
            # Cluster Search
            new_parameters = copy.deepcopy(params)
            new_parameters["search_switches"] = False
            new_parameters["cluster"] = True
            new_parameters["blockedCharacteristics"].clear()
            new_parameters["fixedVariables"].clear()
            new_parameters["countered_trails"].clear()
            cipher.create_cluster_parameters(new_parameters, characteristic)

            solutions, solutions_counter = check_solutions(new_parameters, cipher, lunch_arg['threshold'],
                                                           lunch_arg['cluster_count'])
            if params["search_switches"]:
                print("solutions:{}".format(solutions))
            setattr(characteristic, "previous_trail_count", solutions_counter)

            summing_prob(characteristic, solutions, params)
    checkout_results(params, result_file)


def summing_prob(characteristic, solutions, params):
    weight = (int(characteristic.weight, 16))
    trails = characteristic.getData()
    switch_weight_key = params["em_start_search_num"]
    switch_weight = int(trails[switch_weight_key][10])
    pro = math.pow(2, -2 * (weight - switch_weight) + switch_weight) * solutions
    global TOTAL_PROB
    TOTAL_PROB += pro


def start_search(lunch_arg):
    cipher_name = lunch_arg['cipher']
    cipher = CIPHER_MAPPING[cipher_name]
    util.makedirs(["results", TEMP_DIC, "sharp_tmp"])
    start_round = lunch_arg['startRound']
    end_round = lunch_arg['endRound']
    end_round = start_round + 1 if end_round == -1 else end_round
    switch_rounds = lunch_arg['switchRounds']
    params = copy.deepcopy(lunch_arg)
    for r in range(start_round, end_round):
        if switch_rounds == -1:
            params['switchStartRound'] = -1
        else:

            switch_start_round = int(r / 2) - int(switch_rounds / 2)

            params['switchStartRound'] = switch_start_round
        params['rounds'] = r
        find_single_trail(cipher, r, params)


def loadparameters(args):
    """
    Get parameters from the argument list and inputfile.
    """
    # Load default values
    params = {"cipher": "sand",
              "startRound": 5,
              "endRound": -1,
              "switchRounds": 4,
              "threshold": 6,
              "eachRoundMaxTime": 60 * 60 * 5,
              "eachRoundMaxValid": 2,
              "wordsize": 64,
              "blocksize": 64,
              "sweight": 0,
              "endweight": 1000,
              "iterative": False,
              "boolector": False,
              "dot": None,
              "latex": None,
              "nummessages": 1,
              "timelimit": -1,
              "fixedVariables": {},
              "blockedCharacteristics": [],
              "search_switches": False,
              "countered_trails": []}

    # Check if there is an input file specified
    if args.inputfile:
        with open(args.inputfile[0], 'r') as input_file:
            doc = yaml.load(input_file, Loader=yaml.Loader)
            params.update(doc)
            if "fixedVariables" in doc:
                fixed_vars = {}
                for variable in doc["fixedVariables"]:
                    fixed_vars = dict(list(fixed_vars.items()) +
                                      list(variable.items()))
                params["fixedVariables"] = fixed_vars

    return params


def main():
    parser = ArgumentParser(description="This tool finds the best differential"
                                        "trail in a cryptopgrahic primitive"
                                        "using STP and CryptoMiniSat.",
                            formatter_class=RawTextHelpFormatter)

    parser.add_argument('--inputfile', nargs=1, help="Use an yaml input file to"
                                                     "read the parameters.", default=["sand.yml"])

    args = parser.parse_args()
    params = loadparameters(args)
    start_search(params)


if __name__ == '__main__':
    main()
