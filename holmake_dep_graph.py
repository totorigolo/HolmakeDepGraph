#!/usr/bin/env python3
import collections
from collections import OrderedDict
import random
import os
import re
import sys

''' Holmake dependency graph
'''

config = None


class OrderedSet(collections.MutableSet):
    def __init__(self, iterable=None):
        self.data = OrderedDict()
        if iterable is not None:
            for key in iterable:
                self.data[key] = None

    def __len__(self):
        return len(self.data)

    def __contains__(self, key):
        return key in self.data

    def add(self, key):
        if key not in self.data:
            self.data[key] = None

    def discard(self, key):
        if key in self.data:
            self.data.pop(key)

    def __iter__(self):
        yield from self.data

    def __reversed__(self):
        yield from reversed(self.data)

    def pop(self, last=True):
        if not self:
            raise KeyError('OrderedSet is empty')
        self.data.popitem(last=last)

    def __repr__(self):
        if not self:
            return '%s()' % (self.__class__.__name__,)
        return '%s(%r)' % (self.__class__.__name__, list(self))

    def __eq__(self, other):
        if isinstance(other, OrderedSet):
            return len(self) == len(other) and list(self) == list(other)
        return set(self) == set(other)


def random_color():
    r = random.randint(0, 255)
    g = random.randint(0, 255)
    b = random.randint(0, 255)
    return '#{}'.format(''.join(map(lambda i: format(i, '02X'), [r, g, b])))


def get_all_files_ending_with(base_path, endings):
    result = []

    compiled_path_regex = None
    if config['filter_files'] is not None:
        compiled_path_regex = re.compile(config['filter_files'])

    for path, _, files in sorted(os.walk(base_path)):
        for f in sorted(files):
            absolute_path = os.path.abspath(path)
            absolute_file_path = "/".join((absolute_path, f))
            if compiled_path_regex and not compiled_path_regex.search(absolute_file_path):
                continue
            if any(f.endswith(ending) for ending in endings):
                result.append(absolute_file_path)
    return result


def remove_extension(path):
    path = path.replace('.sml', '')
    path = path.replace('.sig', '')
    path = path.replace('.ui', '')
    path = path.replace('.uo', '')
    return path


def path_to_content(path):
    remove_dependencies_regex = None
    if config['exclude_dependencies'] is not None:
        remove_dependencies_regex = re.compile(config['exclude_dependencies'])

    keep_dependencies_regex = None
    if config['keep_dependencies'] is not None:
        keep_dependencies_regex = re.compile(config['keep_dependencies'])

    with open(path, 'r') as f:
        content = f.readlines()
        content = map(str.strip, content)
        content = map(remove_extension, content)

        if remove_dependencies_regex and keep_dependencies_regex:
            content = filter(
                lambda s: not remove_dependencies_regex.search(s) and keep_dependencies_regex.search(s),
                content)
        elif remove_dependencies_regex:
            content = filter(lambda s: not remove_dependencies_regex.search(s), content)
        elif keep_dependencies_regex:
            content = filter(lambda s: keep_dependencies_regex.search(s), content)

        return list(content)


def prettify_long_name(long_name):
    pretty = long_name

    hol_index = pretty.find('$(HOLDIR)/sigobj/')
    if hol_index >= 0:
        pretty = 'HOL4/' + pretty[hol_index + len('$(HOLDIR)/sigobj/'):]

    hol_ba_index = pretty.find('/HolBA/')
    if hol_ba_index >= 0:
        pretty = pretty[hol_ba_index + 1:]

    return pretty


def get_non_uniques_file_names(paths):
    seen = set()
    non_uniques = OrderedSet()
    for path in paths:
        short = path
        short = prettify_long_name(short)

        filename = short.split('/')[-1]
        if filename in seen:
            non_uniques.add(filename)
        seen.add(filename)
    return non_uniques


def generate_short_unique_name_mapping(long_file_paths):
    if not isinstance(long_file_paths, OrderedSet):
        long_file_paths = OrderedSet(long_file_paths)

    non_uniques_file_names = get_non_uniques_file_names(long_file_paths)
    if len(non_uniques_file_names) > 0:
        print('Non unique file names: {}'.format(non_uniques_file_names), file=sys.stderr)

    mapping = dict()

    for file_path in long_file_paths:
        short = file_path
        short = prettify_long_name(short)

        if short.startswith('HOL4/'):
            mapping[file_path] = short
        else:
            filename = short.split('/')[-1]
            if filename not in non_uniques_file_names:
                mapping[file_path] = filename
            else:
                mapping[file_path] = '/'.join(short.split('/')[-3:])

    return mapping


def flatten(list_):
    return sum(list_, [])


class DependencyGraphNode(object):
    def __init__(self, node_id, dependencies_as_ids):
        self.id = node_id
        self.dependencies = OrderedSet(dependencies_as_ids)
        self.dependents = OrderedSet()


class DependencyGraph(object):
    def __init__(self, mapping, ext_nodes):
        self.path_to_name_mapping = mapping

        self.path_to_id = OrderedDict()
        self.id_to_path = OrderedDict()
        for i, path in enumerate(mapping):
            self.path_to_id[path] = i
            self.id_to_path[i] = path

        self.nodes_by_id = OrderedDict()
        for path, dependencies in ext_nodes:
            node_id = self.path_to_id[path]
            dependencies_as_ids = map(lambda p: self.path_to_id[p], dependencies)

            node = DependencyGraphNode(node_id, dependencies_as_ids)
            self.nodes_by_id[node.id] = node

        # Init nodes dependents
        for node_id, node in self.nodes_by_id.items():
            for dependency_id in node.dependencies:
                self.nodes_by_id[dependency_id].dependents.add(node_id)

    def remove_transitive_dependencies(self):
        def remove_common_dependencies(base_node, node_):
            for dependency_ in node_.dependencies:
                try:
                    base_node.dependencies.remove(dependency_)
                except KeyError:
                    pass
                remove_common_dependencies(base_node, self.nodes_by_id[dependency_])

        for node_id, node in self.nodes_by_id.items():
            for dependency in list(node.dependencies):
                remove_common_dependencies(node, self.nodes_by_id[dependency])

    def as_dot(self):
        dot_lines = list()
        dot_lines.append('digraph G {')

        dot_lines.append('')
        dot_lines.append('# Nodes')
        dot_lines.append('')

        all_files = OrderedSet()
        for node_id, node in self.nodes_by_id.items():
            all_files.add(self.id_to_path[node_id])
            for dependency in node.dependencies:
                all_files.add(self.id_to_path[dependency])

        node_mapping = OrderedDict()
        for i, file_path in enumerate(all_files):
            filename = self.path_to_name_mapping[file_path]
            dot_lines.append('n{}[label="{}"]'.format(i, filename))
            node_mapping[file_path] = 'n{}'.format(i)

        dot_lines.append('')
        dot_lines.append('# Edges')
        dot_lines.append('')

        for node_id, node in self.nodes_by_id.items():
            file_path = self.id_to_path[node_id]
            from_node = node_mapping[file_path]
            edge_color = random_color()
            for dependency_id in node.dependencies:
                dependency = self.id_to_path[dependency_id]
                to_node = node_mapping[dependency]
                dot_lines.append('{} -> {}[color="{}"];'.format(
                    from_node, to_node, edge_color))

        dot_lines.append('}')
        return '\n'.join(dot_lines)


def gen_dependency_graph_in(path):
    print("Generating dependency graph in: {}".format(path), file=sys.stderr)

    ui_uo_files = get_all_files_ending_with(path, ['.uo'])
    nodes = map(lambda f: (remove_extension(f), path_to_content(f)), ui_uo_files)

    # Merge .ui and .uo files
    node_dict = OrderedDict()
    for path, content in nodes:
        if path not in node_dict:
            node_dict[path] = OrderedSet()
        for line in content:
            if line not in node_dict:
                node_dict[line] = OrderedSet()
            node_dict[path].add(line)
    for path in node_dict:
        if path in node_dict[path]:
            node_dict[path].remove(path)

    if config['debug_print_files']:
        for file_path, content in node_dict.items():
            print(file_path, file=sys.stderr)
            for line in content:
                print('  -', line, file=sys.stderr)
            print(file=sys.stderr)

    all_file_paths = []
    for file_path, dependencies in node_dict.items():
        all_file_paths.append(file_path)
        all_file_paths.extend(dependencies)
    all_file_paths = OrderedSet(all_file_paths)

    mapping = generate_short_unique_name_mapping(all_file_paths)

    return DependencyGraph(mapping, node_dict.items())


def work_in(path):
    graph = gen_dependency_graph_in(path)

    if config['remove_transitive_dependencies']:
        graph.remove_transitive_dependencies()

    dot_src = graph.as_dot()

    if config['output']:
        with open(config['output'], 'w') as dot_file:
            dot_file.write(dot_src)
    else:
        print(dot_src)


def parse_arguments():
    import argparse
    parser = argparse.ArgumentParser(
        description=__doc__,
    )

    parser.add_argument(
        'src-root',
        type=str,
        help='The source root where Holmake .uo files will be recursively looked-up'
    )

    parser.add_argument(
        '--output',
        required=False,
        default=None,
        help="Location of the generated dot file (default: stdout)",
    )
    parser.add_argument(
        '--debug-print-files',
        required=False,
        default=False,
        action="store_true",
        help='Useful to write filtering regex'
    )
    parser.add_argument(
        '--remove-transitive-dependencies',
        required=False,
        default=False,
        action="store_true",
    )
    parser.add_argument(
        '--filter-files',
        required=False,
        default=None,
        help='Regex to filter leaf files'
    )
    parser.add_argument(
        '--exclude-dependencies',
        required=False,
        default=None,
        help='Regex to exclude some dependencies'
    )
    parser.add_argument(
        '--keep-dependencies',
        required=False,
        default=None,
        help='Regex to keep some dependencies'
    )
    parser.add_argument(
        '--random-seed',
        required=False,
        default=6737,
        help='Seed for the PRNG (the program is deterministic)'
    )

    global config
    config = vars(parser.parse_args())


def main():
    parse_arguments()
    random.seed(config['random_seed'])
    work_in(config['src-root'])


if __name__ == '__main__':
    main()
