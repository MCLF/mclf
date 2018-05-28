Airspeed Velocity Benchmarks
============================

The benchmarks in this directory are automatically run by CircleCI on the
master branch. The results can be seen at https://mclf.github.io/mclf-asv.

To run the benchmarks in this directory manually, you need to install
[asv](https://github.com/airspeed-velocity/asv) and `sage-asv`
```
sage -pip install asv
pushd .circleci/sage-asv
sage -python setup.py install
popd
```

and then start the benchmarks with
```
sage -sh -c "asv run --quick"
```
