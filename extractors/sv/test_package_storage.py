"""Package singleton identity and static initialization (IEEE 1800-2023, 26)."""
from pathlib import Path
import unittest

import extract
from test_bit_queries import lower, nodes
from test_division import symbolic

# SYNTHETIC-ORACLE: tests=PackageStorage | origin=spec | authority=IEEE-1800-2023#26 | map=identity:bound-original-declaration;singleton:one-static-store;initialization:closed-before-module;imports:no-runtime-copy;invalid:frontend-barrier;boundaries:retained-Unsupported;collision:injective-storage-audit;symbolic:separate-mode


class PackageStorage(unittest.TestCase):
    def test_qualified_imported_and_reexported_names_share_one_slot(self):
        d = lower('package P; int x=2; endpackage '
                  'package R; import P::x; export P::x; endpackage '
                  'module top; import R::*; initial begin x=3; R::x=P::x+1; end endmodule')
        decls = d['modules'][0]['decls']
        self.assertEqual([n['name'] for n in decls], ['$package:1:P:x'])
        self.assertEqual(decls[0]['source_package'], 'P')
        self.assertEqual(decls[0]['source_name'], 'x')
        self.assertTrue(decls[0]['package_storage'])
        self.assertEqual({n['name'] for n in nodes(d) if n.get('kind') == 'Ident'}, {'$package:1:P:x'})
        self.assertFalse(d['others'])

    def test_distinct_packages_and_local_shadowing_do_not_alias(self):
        d = lower('package A; int x=2; endpackage package B; int x=4; endpackage '
                  'module top; import A::*; int x; initial begin x=8; A::x=B::x; end endmodule')
        self.assertEqual([n['name'] for n in d['modules'][0]['decls']],
                         ['$package:1:A:x', '$package:1:B:x', 'x'])
        self.assertEqual({n['name'] for n in nodes(d) if n.get('kind') == 'Ident'},
                         {'x', '$package:1:A:x', '$package:1:B:x'})

    def test_package_declarations_precede_module_initializer_reads(self):
        d = lower('package P; int x=4; endpackage module top; int y=P::x+1; endmodule')
        self.assertEqual([n['name'] for n in d['modules'][0]['decls']], ['$package:1:P:x', 'y'])

    def test_parameter_and_enum_references_are_bound_literals(self):
        d = lower('package P; parameter int N=7; typedef enum logic[2:0] {E=3} T; '
                  'int x=N+1; endpackage module top; import P::*; initial $display("%0d %0d",N,E); endmodule')
        self.assertFalse(any(n.get('kind') == 'Unsupported' for n in nodes(d)))
        self.assertFalse(any(n.get('kind') == 'Ident' for n in nodes(d)))

    def test_imports_at_unit_and_block_scopes_use_original_bindings(self):
        d = lower('package P; int x; endpackage import P::*; '
                  'module top; initial begin import P::x; x=5; end endmodule')
        self.assertFalse(any(n.get('kind') == 'Unsupported' for n in nodes(d)))
        self.assertEqual({n['name'] for n in nodes(d) if n.get('kind') == 'Ident'}, {'$package:1:P:x'})

    def test_runtime_or_effectful_initializers_stay_loud(self):
        for init in ('x+1', 'x++', '1 || f()'):
            d = lower('package P; int x=4; function int f(); return 1; endfunction '
                      'int y='+init+'; endpackage module top; endmodule')
            self.assertIn('Package:initializer', [n.get('sv_kind') for n in nodes(d)])

    def test_unmodelled_package_members_are_not_erased(self):
        for item, wall in [('int a[0:1];', 'Package:storage-type'),
                           ('string a;', 'Package:storage-type'),
                           ('class C; endclass', 'Package:ClassType')]:
            d = lower('package P; '+item+' endpackage module top; endmodule')
            self.assertIn(wall, [n.get('sv_kind') for n in nodes(d)])
        d = lower('package P; function int f(); return 1; endfunction '
                  'endpackage module top; initial $display("%0d", P::f()); endmodule')
        self.assertIn('Package:Subroutine', [n.get('sv_kind') for n in nodes(d)])

    def test_unreferenced_package_subroutines_are_inert(self):
        d = lower('package P; task automatic never_called(); $display("NO"); endtask '
                  'function int also_unused(input int x); return x + 1; endfunction '
                  'endpackage module top; initial $display("PASS"); endmodule')
        self.assertNotIn('Package:Subroutine', [n.get('sv_kind') for n in nodes(d)])
        self.assertEqual([], d['others'])

    def test_imported_package_call_remains_loud(self):
        d = lower('package P; function int f(); return 1; endfunction '
                  'endpackage module top; import P::f; '
                  'initial $display("%0d", f()); endmodule')
        self.assertIn('Package:Subroutine', [n.get('sv_kind') for n in nodes(d)])

    def test_nonintegral_parameter_stays_loud(self):
        d = lower('package P; parameter string S="value"; endpackage module top; endmodule')
        self.assertIn('Package:Parameter', [n.get('sv_kind') for n in nodes(d)])

    def test_invalid_package_and_import_sources_have_a_design_barrier(self):
        for text in ('package P; initial $display("effect"); endpackage',
                     'package P; int x; endpackage module top; import P::absent; endmodule',
                     'package P; int x; endpackage module top; initial missing=1; endmodule'):
            d = lower(text, require_valid=False)
            self.assertIn('Package:invalid-compilation', [n.get('sv_kind') for n in nodes(d)])

    def test_conflicting_import_warnings_still_prevent_execution(self):
        for imports in ('import A::x; import B::x;', 'import A::x; int x;'):
            d = lower('package A; int x; endpackage package B; int x; endpackage '
                      'module top; '+imports+' endmodule')
            self.assertIn('Package:invalid-compilation', [n.get('sv_kind') for n in nodes(d)])

    def test_unexported_bindings_cannot_leak_through_later_imports(self):
        for imported in ('import B::*;', 'import B::x;'):
            d = lower('package A; int x=2; endpackage package B; import A::x; endpackage '
                      'module top; '+imported+' initial $display("%0d",x); endmodule')
            self.assertIn('Package:import-visibility', [n.get('sv_kind') for n in nodes(d)])

    def test_wildcard_export_and_export_all_preserve_original_bindings(self):
        for exported in ('export A::*;', 'export *::*;'):
            d = lower('package A; int x; endpackage package B; import A::x; '+exported+
                      ' endpackage module top; import B::*; initial x=7; endmodule')
            self.assertFalse(any(n.get('kind') == 'Unsupported' for n in nodes(d)))
            self.assertEqual({n['name'] for n in nodes(d) if n.get('kind') == 'Ident'}, {'$package:1:A:x'})

    def test_partial_export_does_not_forward_unreferenced_candidates(self):
        d = lower('package A; int x; int y; endpackage '
                  'package B; import A::*; export A::x; endpackage '
                  'module top; import B::*; initial x=7; endmodule')
        self.assertFalse(any(n.get('kind') == 'Unsupported' for n in nodes(d)))
        self.assertEqual({n['name'] for n in nodes(d) if n.get('kind') == 'Ident'}, {'$package:1:A:x'})

    def test_transparent_enum_members_can_be_imported_explicitly(self):
        d = lower('package A; typedef enum {ZERO,ONE} T; endpackage '
                  'module top; import A::T, A::ONE; T value; initial value=ONE; endmodule')
        self.assertFalse(any(n.get('kind') == 'Unsupported' for n in nodes(d)))

    def test_qualified_unexported_access_and_own_explicit_import_remain_valid(self):
        d = lower('package A; int x=2; endpackage package B; import A::x; int y=4; endpackage '
                  'module top; import B::y; initial $display("%0d %0d",B::x,y); endmodule')
        self.assertFalse(any(n.get('kind') == 'Unsupported' for n in nodes(d)))

    def test_reserved_storage_collision_remains_loud(self):
        d = lower('package P; int x; endpackage module top; int \\$package:1:P:x ; endmodule')
        self.assertIn('Package:storage-collision', [n.get('sv_kind') for n in nodes(d)])

    def test_multiple_modules_do_not_get_independent_copies(self):
        d = lower('package P; int x; endpackage module a; endmodule module b; endmodule')
        self.assertIn('Package:multiple-modules', [n.get('sv_kind') for n in nodes(d)])
        self.assertFalse(any(n.get('package_storage') for n in nodes(d)))

    def test_bindings_are_restored_and_repeated_runs_are_identical(self):
        text = 'package P; int x; endpackage module top; initial P::x=1; endmodule'
        first = lower(text)
        lower('module top; int x; endmodule')
        self.assertEqual(first, lower(text))
        self.assertEqual(extract._PACKAGE_BINDINGS, {})
        self.assertEqual(extract._PACKAGE_SCOPES, set())

    def test_escaped_package_names_do_not_collide(self):
        d = lower('package \\A:B ; int x; endpackage package A; int \\B:x ; endpackage '
                  'module top; endmodule')
        self.assertEqual([n['name'] for n in d['modules'][0]['decls']],
                         ['$package:3:A:B:x', '$package:1:A:B:x'])

    def test_symbolic_mode_keeps_its_existing_package_surface(self):
        d = symbolic('package P; parameter int N=4; endpackage '
                     'module divider; import P::*; logic[N-1:0] x; endmodule')
        self.assertFalse(any(n.get('package_storage') for n in nodes(d)))
        self.assertTrue(any(n.get('kind') == 'ParamRef' for n in nodes(d)))

    def test_authored_acceptance_sources(self):
        root = Path(__file__).resolve().parents[2] / 'Examples/system-verilog/package_storage'
        for name in ('identity', 'defaults', 'packed', 'timers'):
            d = lower((root/(name+'.sv')).read_text())
            self.assertFalse(any(n.get('kind') == 'Unsupported' for n in nodes(d)), name)
        d = lower((root.parent/'package_unused_subroutines' /
                   'package_unused_subroutines.sv').read_text())
        self.assertFalse(any(n.get('kind') == 'Unsupported' for n in nodes(d)))


if __name__ == '__main__':
    unittest.main()
