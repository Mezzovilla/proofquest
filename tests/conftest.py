def pytest_addoption(parser):
    parser.addoption(
        "--run-integration",
        action="store_true",
        default=False,
        help="run real repository integration tests requiring network, git and Lean",
    )
