import argparse
import json
from unicodedata import name


def main() -> None:
    parser = argparse.ArgumentParser(description='Script to unify jsons.')

    parser.add_argument('--jsons-list', '-j',
                        type=str,
                        default=[],
                        help='List of jsons to unify',
                        nargs='*')

    arguments = parser.parse_args()
    
    jsons = arguments.jsons_list
    
    instances = [f'ins-{i}' for i in range(1,41)]
    
    resulting_json = {i: {} for i in instances}
    
    for j in jsons:
        with open(j, 'r') as f:
            js = json.load(f)
            for i in instances:
                if i in js:
                    for k in js[i]:
                        resulting_json[i][k] = js[i][k]
                        
    with open('unified_json.json', 'w') as f:
        json.dump(resulting_json, f, sort_keys=False, indent=4, separators=(',', ': '))

if __name__ == '__main__':
    main()