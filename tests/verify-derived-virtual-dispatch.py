#!/usr/bin/env python3
"""Regression gate for Rewind's derived-class virtual-slot and dominating type-test recovery."""
from __future__ import annotations
import argparse, csv, sys
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('--behavior-report', required=True, type=Path)
p.add_argument('--behavior-source', required=True, type=Path)
p.add_argument('--astar-report', required=True, type=Path)
p.add_argument('--astar-source-root', required=True, type=Path)
a = p.parse_args()

def rows(path: Path):
    with path.open(newline='', encoding='utf-8') as f:
        return [r for r in csv.reader(f, delimiter='\t') if len(r) >= 4]

def reasons(rs, signature):
    return [r[2] for r in rs if signature in r[-1]]

def require(condition, message):
    if not condition:
        raise SystemExit('FAIL: ' + message)
    print('PASS: ' + message)

br, ar = rows(a.behavior_report), rows(a.astar_report)
# Calls guarded by Task is ParentTask / Task is Composite must resolve to the guarded base contract.
for method in ['BehaviorManager::Tick', 'BehaviorManager::ReevaluateParentTasks', 'BehaviorManager::PushTask']:
    require(not reasons(br, method), f'{method} has no remaining recovery gap')
for method in ['BehaviorManager::RunTask', 'BehaviorManager::RunParentTask', 'BehaviorManager::PopTask']:
    rs = reasons(br, method)
    require(not any('virtual slot' in x or 'VTable value used as data' in x for x in rs),
            f'{method} has no unresolved virtual dispatch')

bs = a.behavior_source.read_text(encoding='utf-8')
require('internal int AddToTaskList(' in bs, 'ILSpy source preparation emits AddToTaskList instead of rejecting the entire method')
require('part(s) of this method were not recovered' in bs, 'AddToTaskList keeps explicit gap markers; no missing logic is silently hidden')
for snippet in ['((ParentTask)task3).OverrideStatus()', '((ParentTask)task).CanRunParallelChildren()',
                '((Composite)task3).OnReevaluationStarted()', '((ParentTask)task).OverrideStatus(TaskStatus.Running)']:
    require(snippet in bs, f'generated BehaviorDesigner source contains {snippet}')

# A* paths where the receiver is proven to be an ABPath must resolve; don't guess across unrelated GraphNode branches.
for method in ['Pathfinding.AIBase::SetPath', 'Pathfinding.AIPath::OnPathComplete', 'Pathfinding.RichAI::OnPathComplete']:
    require(not any('virtual slot 27' in x or 'VTable value used as data' in x for x in reasons(ar, method)),
            f'{method} has no unresolved derived ABPath dispatch')
for method, slot in [('Pathfinding.RichFunnel::FindWalls', 'virtual slot 21'),
                     ('Pathfinding.GridStringPulling::Calculate', 'virtual slot 23')]:
    require(any(slot in x for x in reasons(ar, method)),
            f'{method} remains conservatively unresolved ({slot}); no cross-branch guess')
require(any('virtual slot 5' in x for x in reasons(br, 'BehaviorManager::OverrideSharedVariable')),
        'unknown SharedVariable receiver remains conservatively unresolved')
print('PASS: derived virtual dispatch regression gate complete')
