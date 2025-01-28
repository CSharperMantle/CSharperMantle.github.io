module Jekyll
  module LengthFilter
    def length(input)
      (!input.nil? && input.kind_of?(Array)) ? input.length : 0
    end
  end
end

Liquid::Template.register_filter(Jekyll::LengthFilter)
