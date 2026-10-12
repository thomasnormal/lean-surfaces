# Retained waiting targets

The region scheduler records the target reached by a suspended process in the
same `ProcState` that owns its residual statement continuation. Edge
sensitivities remain fixed registrations. A `#d` trigger is converted to an
absolute deadline at the suspension time, so advancing time cannot shorten or
restart the wait.

`wakeEdges` delivers only an unsuspended matching edge and clears the
registration before putting the process in Active. `wakeTimers` delivers an
unsuspended deadline at or before the current simulation time in the same
way. A process-control suspension over one of those two waiting targets sets a
separate explicit flag, removes a ready carrier, and leaves the residual,
world effects, NBA queue, and registration untouched. An edge occurring while
that flag is set is not latched. Resuming an edge waiter only clears the flag;
a timer whose original deadline is already due is scheduled in Active at
resume, while a future deadline is retained unchanged.

This public rule intentionally refuses ready-process suspension, level-wait
re-evaluation, terminal or duplicate suspension, and all self/deferred,
join/await, fixed-sensitivity, and process-status cases not represented by the
current interface. Those branches remain loud rather than being approximated.
Already queued nonblocking assignments remain in the world queue and are not
process activations.

The zero-delay `#0` path remains loud: delivering it in Inactive rather than
Active needs a separate region rule and is not smuggled into this target rule.

The driver invokes timer delivery at each ordinary slot boundary. It does not
invent a time advance: callers that model timed slots advance `SvWorld.time`
through the existing primitive, after which the due-target rule is applied.

## Public transition contract

For the admitted waiting-target subset, an explicit suspend transition has the
following shape:

* the process remains in its existing suspended phase with the complete
  residual continuation, signal state, NBA queue, output and registration;
* an edge registration is desensitized by the explicit flag, so an occurrence
  while suspended is not remembered as a wake;
* a timer registration keeps its absolute deadline, including when time
  advances past that deadline;
* resume clears only the explicit flag for an edge or future timer, while a
  due or expired timer is published once into Active at the current time.

The implementation rejects a ready or finished process, a duplicate suspend or
resume, a level wait, and any target without one of these fixed registrations.
These are intentional loud boundaries, not alternate approximations of §9.7.
