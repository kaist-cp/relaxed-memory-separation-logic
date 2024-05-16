# Copied from https://gitlab.mpi-sws.org/iris/diaframe

from collections import defaultdict
import glob, os
import csv
import sys


# categories
IMPLEMENTATION = 1
ANNOTATION = 2
BOILERPLATE = 4
CUSTOMIZATION = 3
CLIENTREUSE = 5
MY_STAT_HEADERS = {IMPLEMENTATION, ANNOTATION, BOILERPLATE, CUSTOMIZATION, CLIENTREUSE}

HINTS = 5.3
BUILD_TIME = 6.5
TOTAL = 6
IRIS_TOTAL = 7
STARLING_TOTAL = 8
PROOF_TBL = 7
PROOF_OLD = 8
BUILD_TIME_OLD = 8.5
CAPER_IMPL = 9
CAPER_ANNOT = 10
CAPER_TOTAL = 11
CAPER_PROOF = 12
VOILA_IMPL = 12
VOILA_TOTAL = 13
# order of table columns is decided by sorted order of above

# subcategories
REGULAR = 'REGULAR'
PROOF = 'PROOF'
BLANK = 'BLANK'

HEADERS = {
    IMPLEMENTATION: 'impl',
    ANNOTATION: 'annot',
    CUSTOMIZATION: 'custom',
    BOILERPLATE: 'boilerplate',
    CLIENTREUSE: 'reuse',
    HINTS: 'hints',
    BUILD_TIME: 'time',
    TOTAL: r'total',
    PROOF_TBL: r'proof',
    PROOF_OLD: r'\thead{old \\ proof}',
    BUILD_TIME_OLD: r'\thead{old \\ time}',
    # IRIS_TOTAL: r'\thead{iris manual \\ total}',
    # STARLING_TOTAL: r'\thead{starling \\ total}',
    # CAPER_IMPL: r'\thead{caper \\ impl}',
    CAPER_ANNOT: r'\thead{caper \\ annot}',
    CAPER_TOTAL: r'\thead{caper \\ total}',
    CAPER_PROOF: r'\thead{caper \\ proof}',
    # VOILA_TOTAL: r'\thead{voila \\ total}',
    # VOILA_IMPL: r'\thead{voila \\ impl}'
}
SUBCAT_HEADERS = {REGULAR: '  ', BLANK: '  ', PROOF: '-P'}
PRINT_HEADERS =  {IMPLEMENTATION: 'IMPL', ANNOTATION: 'ANNO', CUSTOMIZATION: 'CUST', BOILERPLATE: 'BOIL', CLIENTREUSE: 'REUS'}

HIDDEN_COLS = {BOILERPLATE, CLIENTREUSE, CUSTOMIZATION, ANNOTATION}

DISJ_FILES = {
    'arc',
    'barrier',
    'clh_lock',
    'mcs_lock',
    'peterson',
    'rwlock_duolock',
    'rwlock_lockless_faa',
    'rwlock_ticket_bounded',
    'rwlock_ticket_unbounded',
    'ticket_lock',
}


def determine_line_subcat(line):
    stripped_line = line.strip()
    if not stripped_line:
        return BLANK
    elif 'Proof' in stripped_line and not stripped_line.startswith('Set'):
        return PROOF
    elif 'Next Obligation' in stripped_line:
        return PROOF
    else:
        return None


def determine_line_cat(line):
    stripped_line = line.strip()
    if not stripped_line:
        return None
    first_word = stripped_line.split()[0]
    if '_reuse' in stripped_line:
        return CLIENTREUSE
    if first_word == 'From':
        return BOILERPLATE
    elif first_word == 'Definition' or first_word == 'Fixpoint':
        if ': val :=' in line:
            return IMPLEMENTATION
        elif 'iProp' in line :
            return ANNOTATION
    elif first_word == 'Lemma' :
        return CUSTOMIZATION
    elif first_word == 'Ltac':
        return CUSTOMIZATION
    elif first_word == 'Hint':
        return CUSTOMIZATION
    elif first_word == 'Section':
        return BOILERPLATE
    elif first_word == 'End':
        return BOILERPLATE
    elif first_word == 'Context':
        return BOILERPLATE
    elif first_word == 'Class' and 'G' in line:
        return ANNOTATION
    elif 'Obligation Tactic' in line:
        return BOILERPLATE
    elif first_word == 'Existing':  # existing instance
        return ANNOTATION
    elif 'Instance' in line:
        if '_spec' in line:
            return ANNOTATION
        elif 'subG' in line:
            return ANNOTATION
        elif 'persistent' in line.lower():
            return ANNOTATION
        elif 'contractive' in line.lower():
            return ANNOTATION
        elif 'nonexpansive' in line.lower():
            return ANNOTATION
        elif 'timeless' in line.lower():
            return ANNOTATION
        else:
            return CUSTOMIZATION
    return None


def determine_line_cats(line):
    line_cat = determine_line_cat(line)
    line_subcat = determine_line_subcat(line)
    if line_cat is not None:
        line_subcat = line_subcat or REGULAR
    return line_cat, line_subcat


def lines_with_cat(filename):
    with open(filename, 'r') as f:
        current_line_cat = None
        current_line_subcat = None
        all_lines = f.readlines()
        last_non_zero_idx = next((i for i, line in reversed(list(enumerate(all_lines))) if line.strip()))
        actual_lines = all_lines[:last_non_zero_idx+1]
        for line in actual_lines:
            new_line_cat, new_line_subcat = determine_line_cats(line)
            new_line_cat = new_line_cat or current_line_cat
            new_line_subcat = new_line_subcat or current_line_subcat
            if new_line_cat is None or new_line_subcat is None:
                raise ValueError(f'Cannot determine line cats of {line}, line #{idx}')
            yield new_line_cat, new_line_subcat, line
            current_line_cat = new_line_cat
            current_line_subcat = new_line_subcat


def count_lines(filename):
    result = {h: defaultdict(lambda: 0) for h in MY_STAT_HEADERS}
    no_lines = 0
    for line_cat, line_subcat, _ in lines_with_cat(filename):
        no_lines += 1
        result[line_cat][line_subcat] += 1
    assert(sum(map(lambda r: sum(r.values()), result.values())) == no_lines)
    result = {k: v for k,v in sorted(result.items())}
    return result


def get_file_linecount():
    orig_dir = os.getcwd()
    os.chdir('supplements/diaframe_heap_lang_examples/comparison')
    result = {file: count_lines(file) for file in glob.glob('*.v')}
    os.chdir(orig_dir)
    # now add queue_node_lib stats to queue and msc_queue
    for queue_key in {'queue.v', 'msc_queue.v'}:
        for key, valdict in result['queue_node_lib.v'].items():
            for subkey, subval in valdict.items():
                result[queue_key][key][subkey] += subval
    del result['queue_node_lib.v']
    return result


from datetime import timedelta
import math

def pretty_time(seconds):
    # if seconds > 60:
    #     return f'{seconds // 60:.0f}m {seconds%60:.1f}s'
    # else:
    #     return f'{seconds:.1f}s'
    return f'{seconds // 60:.0f}:{math.ceil(seconds%60):02.0f}'


def as_tabulate_row(info, extra_info):
    if CUSTOMIZATION in info and sum(info[CUSTOMIZATION].values()) != 0:
        info[CUSTOMIZATION] = {PROOF: sum(info[CUSTOMIZATION].values())}
    result = {
        col: '{}/{}'.format(sum(key.values()), key[PROOF]) if (PROOF in key and col != CUSTOMIZATION) else
            (str(sum(key.values())) if sum(key.values()) != 0 else '')
        for col, key in info.items()
        if col not in HIDDEN_COLS
    }
    result[TOTAL] = sum(map(lambda d: sum(d.values()), info.values()))
    result[PROOF_TBL] = sum((
        (d[PROOF] if PROOF in d else 0) if key != CUSTOMIZATION else sum(d.values())
        for key, d in info.items()
    ))

    # hint_str = str(extra_info['num_hints']) if int(extra_info['num_hints']) else ''
    # if int(extra_info['custom_hints']) > 0:
    #     hint_str += '({})'.format(extra_info['custom_hints'])
    # result[HINTS] = hint_str
    result[BUILD_TIME] = pretty_time(float(extra_info['build_seconds']))
    # if extra_info['starling_total']:
    #     result[STARLING_TOTAL] = '{}/{}'.format(
    #         extra_info['starling_total'],
    #         extra_info['starling_proof'],
    #     )
    # else:
    #     result[STARLING_TOTAL] = ''
    if 'caper_impl'in extra_info and extra_info['caper_impl']:
        result[CAPER_IMPL] = extra_info['caper_impl']
        # result[CAPER_ANNOT] = extra_info['caper_annot']
        result[CAPER_TOTAL] = extra_info['caper_total']
        result[CAPER_PROOF] = extra_info['caper_proof']
    elif 'caper_impl' in extra_info:
        result[CAPER_IMPL] = ''
        result[CAPER_TOTAL] = ''
        result[CAPER_PROOF] = ''
    if 'old_proof' in extra_info:
        result[PROOF_OLD] = extra_info['old_proof']
        result[BUILD_TIME_OLD] = pretty_time(float(extra_info['old_build_seconds']))
    else:
        result[PROOF_OLD] = ''
        result[BUILD_TIME_OLD] = ''
    # if extra_info['voila_total']:
    #     result[VOILA_TOTAL] = '{}/{}'.format(
    #         extra_info['voila_total'],
    #         extra_info['voila_proof'],
    #     )
    # else:
    #     result[VOILA_TOTAL] = ''
    # if 'voila_impl'in extra_info and extra_info['voila_impl']:
    #     result[VOILA_IMPL] = extra_info['voila_impl']
    # elif 'voila_impl' in extra_info:
    #     result[VOILA_IMPL] = ''
    # if extra_info['iris_total']:
    #     result[IRIS_TOTAL] = '{}/{}'.format(
    #         extra_info['iris_total'],
    #         extra_info['iris_proof']
    #     )
    # else:
    #     result[IRIS_TOTAL] = ''
    return {k: v for k, v in sorted(result.items()) if k in HEADERS}


def load_additional_stats():
    with open('other_tools_data.csv') as f:
        rows = list(csv.reader(f, delimiter=','))
        header_dict = {i: col for i, col in enumerate(rows[0])}
        result_pre = [
            {header_dict[i]: col for i, col in enumerate(row)}
            for row in rows[1:]
        ]
        return {
            result['Program']: result
            for result in result_pre
        }


REFERENCES = {
    'arc': 'arc__rust',
    'bag_stack': 'treiber_stack__treiber_1986',
    'clh_lock': 'clh_lock__magnusson_1994',
    'lclist': 'lclist_rgsep_thesis__vafeiadis_2008, smallfootrg__calcagno_2007',
    'mcs_lock': 'mcs_lock__mellor_crumney_1991',
    'msc_queue': 'msc_queue__michael_1996',
    'peterson': 'peterson_algorithm__peterson_1981',
    'rwlock_duolock': 'rwlocks__courtois_1971',
}


def get_row_name(rawfilename, table_fmt):
    # -2 cuts off .v extension
    no_ext = rawfilename[:-2]
    result = no_ext.replace(r'_', r'\_')
    if no_ext in DISJ_FILES:
        result = f'\\textbf{{{result}}}'
    if no_ext in REFERENCES and table_fmt and table_fmt.startswith('latex'):
        result += f'{{\small \\citep{{{REFERENCES[no_ext]}}}}}'
    return result


ADDITIONAL_STAT_HEADERS = {
    # 'starling_total', 'starling_proof',
    'caper_impl',
    'caper_proof',
    'caper_total',
    'old_proof',
    'old_build_seconds',
    # 'voila_impl',
    # 'voila_total', 'voila_proof', 'iris_total', 'iris_proof',
    # 'num_hints',
    # 'custom_hints',
    'build_seconds',
}


def get_total_info(my_stats, other_stats):
    return {
        header: {
            subheader: sum((my_stats[file][header][subheader] for file in my_stats.keys() if subheader in my_stats[file][header] and file[:-2] in other_stats))
            for subheader in SUBCAT_HEADERS.keys()
        }
        for header in MY_STAT_HEADERS
    }

def to_num(near_num):
    try:
        return int(near_num)
    except ValueError:
        return float(near_num)


def get_stats_table(table_fmt=None):
    from tabulate import tabulate
    my_stats = get_file_linecount()
    other_stats = load_additional_stats()
    tabulate_input = [
        {'name': get_row_name(file, table_fmt), **as_tabulate_row(info, other_stats[file[:-2]])}
        for file, info in sorted(my_stats.items())
        if file[:-2] in other_stats
    ]
    total_info = get_total_info(my_stats, other_stats)
    for header in total_info.keys():
        for subheader in list(total_info[header].keys()):
            if not total_info[header][subheader]:
                del total_info[header][subheader]  # makes m/0 print like m
    additional_totals = {
        header: sum((to_num(other_stats[file][header]) for file in other_stats.keys() if other_stats[file][header]))
        for header in ADDITIONAL_STAT_HEADERS
    }
    total_row = as_tabulate_row(total_info, additional_totals)
    # total_row[HINTS] = '38(8)'  # hardcoded, but this is hard to compute here..
    tabulate_input.append(
        {'name': 'total', **total_row}
    )
    return tabulate(tabulate_input, headers=HEADERS, tablefmt=table_fmt
    , colalign=['left', 'right', 'right', 'right', 'right', 'right', 'right', 'right'])


def print_file_with_cats(filename):
    for line_cat, line_subcat, line in lines_with_cat(filename):
        print(PRINT_HEADERS[line_cat] + SUBCAT_HEADERS[line_subcat], line.rstrip())
    print()

    other_stats = load_additional_stats()
    line_count = count_lines(filename)
    for key, d in line_count.items():
        print(f'{HEADERS[key]}: {sum(d.values())}/{d[PROOF]}')


def get_proof_burden_stats(example_data):
    total_proof_burden = sum(((example_data[col][PROOF] if PROOF in example_data[col] else 0) if col != CUSTOMIZATION else sum(example_data[col].values()) for col in example_data.keys()))
    total_implementation = sum(example_data[IMPLEMENTATION].values())
    return total_proof_burden, total_implementation, total_proof_burden / total_implementation


def calculate_statistics():
    my_stats = get_file_linecount()
    total_info = get_total_info(my_stats)
    total_proof_burden, total_implementation, avg_burden_per_loc = get_proof_burden_stats(total_info)
    examples_proof_per_loc = {file: get_proof_burden_stats(data)[2] for file, data in my_stats.items() if file != 'k42_lock.v'}
    min_burden = min(examples_proof_per_loc.values())
    min_burden_files = {file for file in my_stats.keys() if file in examples_proof_per_loc and examples_proof_per_loc[file] == min_burden}
    max_burden = max(examples_proof_per_loc.values())
    print(f'Minimum proof-burden/LOC: {min_burden} for { len(min_burden_files) } examples: { min_burden_files }')
    print(f'Average proof-burden/LOC: {avg_burden_per_loc}')
    print(f'Maximum proof-burden/LOC: {max_burden} for { {file for file in my_stats.keys() if file in examples_proof_per_loc and examples_proof_per_loc[file] == max_burden} }')
    print(f'Number of examples with proof-burden/LOC < 0.4: {sum((1 for brdn in examples_proof_per_loc.values() if brdn < 0.4))}')


def main():
    if len(sys.argv) == 1:
        print(get_stats_table())
    elif len(sys.argv) == 2:
        arg = sys.argv[1]
        if arg.startswith('--'):
            fmt = arg[2:]
            if fmt == 'help':
                print('''Usage:
python utils/stats_gen.py --help            shows this message
python utils/stats_gen.py                   displays a bash-readable table
python utils/stats_gen.py --latex           displays a latex-renderable table
python utils/stats_gen.py --statistics      calculates some statistics
python utils/stats_gen.py <filepath>        prints the file, with annotations indicating each line with its type: annotation/proof/implmentation/etc''')
            elif fmt == 'statistics':
                calculate_statistics()
            elif fmt == 'latex':
                print(get_stats_table('latex_raw'))
            else:
                raise ValueError(f'Unknown format {fmt}')
        else:
            print_file_with_cats(arg)


if __name__ == '__main__':
    main()
# print(print_file_with_cats('theories/examples/comparison/clh_lock.v'))
