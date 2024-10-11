class Func
  def initialize(arr)
    @tt, @tf, @ft, @ff = arr
  end

  def use(a, b)
    if a && b
      @tt
    elsif a && !b
      @tf
    elsif !a && b
      @ft
    else
      @ff
    end
  end
end

tf = [true, false]

funcs = tf.repeated_permutation(4).map { Func.new _1 }

funcs.filter do |fn|
  tf.repeated_permutation(2).any? { |a, b| fn.use(a, b) != fn.use(b, a) } &&
  tf.repeated_permutation(3).any? do |a, b, c|
    fn.use(a, fn.use(b, c)) != fn.use(fn.use(a, b), c)
  end &&
  tf.repeated_permutation(3).all? do |a, b, c|
    fn.use(a, fn.use(b, c)) == fn.use(b, fn.use(a, c))
  end
end.each { p _1 }
