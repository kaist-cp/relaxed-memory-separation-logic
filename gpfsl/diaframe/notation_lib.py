from itertools import product


def generate_notation(format_string, dict_iters):
    for entry_comb in product(*dict_iters):
        combined_dict = {k: v for d in entry_comb for k, v in d.items()}
        print(format_string.format(**combined_dict))
