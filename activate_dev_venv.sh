#!/usr/bin/env bash

if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
    echo "ERROR: ${BASH_SOURCE[0]} should be sourced, not executed!"
    exit 1
fi

function _activate_dev_venv {
    _SCRIPT_DIR="$(realpath `dirname "${BASH_SOURCE[0]}"`)"
    _VENV_DIR="${_SCRIPT_DIR}/.dev_venv"

    if [ ! -d "${_VENV_DIR}" ]; then
        if python3 -m venv "${_VENV_DIR}"; then
            echo "INFO: Created development venv at ${_VENV_DIR}"
        else
            echo "ERROR: Couldn't create development venv at ${_VENV_DIR}"
            return 1
        fi
    fi

    if source "${_VENV_DIR}/bin/activate"; then
        echo "INFO: Activated development venv ${_VENV_DIR}"
    else
        echo "ERROR: Couldn't activate development venv ${_VENV_DIR}"
        return 1
    fi

    # Always install packages after activating venv, in case a new packages are
    # added
    _PIP_REQUIREMENTS="${_SCRIPT_DIR}/dev_requirements.txt"
    if pip install -r "${_PIP_REQUIREMENTS}"; then
        echo "INFO: Successfully installed required packages"
    else
        echo "ERROR: Couldn't install all required packages"
        return 1
    fi
    if pre-commit install; then
        echo "INFO: Successfully installer pre-commit hooks"
    else
        echo "ERROR: Couldn't install pre-commit hooks"
        return 1
    fi
    return 0
}

_activate_dev_venv || echo "ERROR: Some error occured"
