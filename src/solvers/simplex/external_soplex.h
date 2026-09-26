/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */
#ifndef __EXTERNAL_SOPLEX_H
#define __EXTERNAL_SOPLEX_H
#ifndef HAVE_SOPLEX
#error "SoPlex library is not available. Please install it to use this feature."
#endif

#include "solvers/simplex/external_simplex_types.h"
#include "solvers/simplex/simplex_types.h"

void spx_solve(simplex_solver_t *solver, external_solution_t *sol);

/**
 * Performs any necessary cleanup for the SoPlex library.
 * This function should be called from the `yices_exit` function
 * to ensure that all resources allocated by the QSopt_ex library
 * are properly released.
 * The function is idempotent,
 * meaning that it can be called multiple times without adverse effects.
 */
void global_spx_clear();

#endif // __EXTERNAL_SOPLEX_H
