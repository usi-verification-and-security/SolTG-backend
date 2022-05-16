add_executable (tgnonlin NonlinSolver.cpp)
target_link_libraries (tgnonlin ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB})
install(TARGETS tgnonlin RUNTIME DESTINATION bin)
